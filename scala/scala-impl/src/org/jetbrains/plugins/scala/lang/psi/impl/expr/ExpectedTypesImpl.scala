package org.jetbrains.plugins.scala.lang.psi.impl.expr

import com.intellij.psi._
import com.intellij.psi.impl.source.tree.LeafPsiElement
import com.intellij.psi.util.PsiTreeUtil
import org.jetbrains.plugins.scala.project.ProjectPsiElementExt
import org.jetbrains.plugins.scala.project.ScalaLanguageLevel.Scala_2_13
import org.jetbrains.plugins.scala.extensions.{ObjectExt, PsiElementExt, PsiTypeExt, SeqExt}
import org.jetbrains.plugins.scala.lang.psi.ScalaPsiUtil.inNameContext
import org.jetbrains.plugins.scala.lang.psi.api.InferUtil
import org.jetbrains.plugins.scala.lang.psi.api.base.ScConstructorInvocation
import org.jetbrains.plugins.scala.lang.psi.api.base.patterns.ScCaseClause
import org.jetbrains.plugins.scala.lang.psi.api.base.types.{ScSequenceArg, ScTupleTypeElement, ScTypeElement}
import org.jetbrains.plugins.scala.lang.psi.api.expr.ExpectedTypes._
import org.jetbrains.plugins.scala.lang.psi.api.expr._
import org.jetbrains.plugins.scala.lang.psi.api.statements._
import org.jetbrains.plugins.scala.lang.psi.api.statements.params.{ScClassParameter, ScParameter, ScParameterClause}
import org.jetbrains.plugins.scala.lang.psi.api.toplevel.typedef.ScMember
import org.jetbrains.plugins.scala.lang.psi.api.toplevel.{ScEarlyDefinitions, ScTypedDefinition}
import org.jetbrains.plugins.scala.lang.psi.impl.ScalaPsiManager
import org.jetbrains.plugins.scala.lang.psi.impl.expr.ExpectedTypesImpl._
import org.jetbrains.plugins.scala.lang.psi.impl.toplevel.synthetic.ScSyntheticFunction
import org.jetbrains.plugins.scala.lang.psi.impl.toplevel.typedef.TypeDefinitionMembers
import org.jetbrains.plugins.scala.lang.psi.implicits.ImplicitResolveResult
import org.jetbrains.plugins.scala.lang.psi.types.api._
import org.jetbrains.plugins.scala.lang.psi.types.api.designator.ScDesignatorType
import org.jetbrains.plugins.scala.lang.psi.types.nonvalue.{Parameter, ScMethodType, ScTypePolymorphicType}
import org.jetbrains.plugins.scala.lang.psi.types.recursiveUpdate.ScSubstitutor
import org.jetbrains.plugins.scala.lang.psi.types.result._
import org.jetbrains.plugins.scala.lang.psi.types.{api, _}
import org.jetbrains.plugins.scala.lang.psi.{ElementScope, ScalaPsiUtil}
import org.jetbrains.plugins.scala.lang.refactoring.util.ScalaNamesUtil
import org.jetbrains.plugins.scala.lang.resolve.MethodTypeProvider._
import org.jetbrains.plugins.scala.lang.resolve.processor.DynamicResolveProcessor._
import org.jetbrains.plugins.scala.lang.resolve.processor.MethodResolveProcessor
import org.jetbrains.plugins.scala.lang.resolve.{ScalaResolveResult, ScalaResolveState, StdKinds}
import org.jetbrains.plugins.scala.macroAnnotations.{CachedWithRecursionGuard, ModCount}
import org.jetbrains.plugins.scala.util.SAMUtil

import scala.annotation.tailrec
import scala.collection.mutable.ArrayBuffer

/**
 * @author ilyas
 *
 * Utility class to calculate expected type of any expression
 */

class ExpectedTypesImpl extends ExpectedTypes {
  /**
   * Do not use this method inside of resolve or type inference.
   * Using this leads to SOE.
   */
  def smartExpectedType(expr: ScExpression, fromUnderscore: Boolean = true): Option[ScType] =
    smartExpectedTypeEx(expr, fromUnderscore).map(_._1)

  def smartExpectedTypeEx(expr: ScExpression, fromUnderscore: Boolean = true): Option[ParameterType] = {
    val types = expectedExprTypes(expr, withResolvedFunction = true, fromUnderscore = fromUnderscore)

    onlyOne(types, expr)
  }

  def expectedExprType(expr: ScExpression, fromUnderscore: Boolean = true): Option[ParameterType] = {
    val types = expr.expectedTypesEx(fromUnderscore)

    onlyOne(types, expr)
  }

  private def onlyOne(types: Seq[ParameterType], place: PsiElement): Option[ParameterType] =
    if (types.isEmpty) None
    else {
      val distinct =
        types.sortBy {
          case (_: ScAbstractType, _) => 1
          case _                      => 0
        }.distinctBy {
          case (ScAbstractType(_, lower, upper), _) if lower == upper => lower
          case (t, _)                                                 => t
        }

      if (distinct.size == 1) distinct.headOption
      else if (place.scalaLanguageLevelOrDefault >= Scala_2_13) {
        val extractor = FunctionLikeType(place)
        val tpes = distinct.map(_._1).toList
        mergeFunctionLikeTpes(tpes, extractor)(place.elementScope)
      } else None
    }


  /** See: https://github.com/scala/scala/pull/6871
   * We only provide an expected type (for each argument position) when:
   * - there is at least one FunctionN type expected by one of the overloads:
   *   in this case, the expected type is a FunctionN[Ti, ?], where Ti are the argument types (they must all be =:=),
   *   and the expected result type is elided using a wildcard.
   *   This does not exclude any overloads that expect a SAM, because they conform to a function type through SAM conversion
   * - OR: all overloads expect a SAM type of the same class, but with potentially varying result types (argument types must be =:=)
   * */
  private[this] def mergeFunctionLikeTpes(
    tpes: List[ScType],
    ftpe: FunctionLikeType
  )(implicit
    scope: ElementScope
  ): Option[ParameterType] = {
    import FunctionTypeMarker._

    def paramTpesMatch(lhs: Seq[ScType], rhs: Seq[ScType]): Boolean =
      lhs.isEmpty ||
        (lhs.size == rhs.size &&
          lhs
            .zip(rhs)
            .forall { case (l, r) => l.equiv(r) })

    @tailrec
    def recur(
      tpes:              List[ScType],
      isFunctionN:       Boolean = false,
      isPartialFunction: Boolean = false,
      isSameSam:         Boolean = true,
      SAMCls:            Option[PsiClass] = None,
      paramTpes:         Seq[ScType] = Seq.empty
    ): Option[ScType] = tpes match {
      case ftpe(marker, _, ptpes) :: rest if paramTpesMatch(paramTpes, ptpes) =>
        val currentSAM = marker match {
          case SAM(cls) => cls.toOption
          case _        => None
        }

        val currentSAMClsMatches = currentSAM.exists(cls =>
          (isSameSam && SAMCls.isEmpty) || SAMCls.contains(cls)
        )

        recur(
          rest,
          isFunctionN || marker == FunctionN,
          isPartialFunction || marker == PF,
          isSameSam && currentSAMClsMatches,
          currentSAM,
          ptpes
        )
      case Nil =>
        if (isPartialFunction) PartialFunctionType((Any, paramTpes.head)).toOption
        else if (isFunctionN)  FunctionType((Any, paramTpes)).toOption
        else if (isSameSam)    SAMCls.map(cls => ScParameterizedType(ScDesignatorType(cls), paramTpes))
        else                   None
      case _ => None
    }

    recur(tpes).map(_ -> None)
  }

  private[this] case class FunctionLikeType(place: PsiElement) {
    import FunctionTypeMarker._

    def unapply(tpe: ScType): Option[(FunctionTypeMarker, ScType, Seq[ScType])] = tpe match {
      case FunctionType(retTpe, paramTpes)       => (FunctionN, retTpe, paramTpes).toOption
      case PartialFunctionType(retTpe, paramTpe) => (PF, retTpe, Seq(paramTpe)).toOption
      case ScAbstractType(_, _, upper)           => unapply(upper)
      case tpe                                   =>
        for {
          (_, retTpe, paramTpes) <- SAMUtil.toSAMType(tpe, place).flatMap(unapply)
          cls                    <- tpe.extractClass
        } yield (SAM(cls), retTpe, paramTpes)
    }
  }

  sealed trait FunctionTypeMarker
  object FunctionTypeMarker {
    case object FunctionN         extends FunctionTypeMarker
    case object PF                extends FunctionTypeMarker
    case class SAM(cls: PsiClass) extends FunctionTypeMarker
  }

  override def expectedParameterType(p: ScParameter): Option[ScType] = p.getContext match {
    case clause: ScParameterClause =>
      clause.getContext.getContext match {
        case fn: ScFunctionExpr =>
          import FunctionTypeMarker.FunctionN

          val functionLikeType = FunctionLikeType(p)
          val eTpe             = fn.expectedType(fromUnderscore = false)
          val idx              = clause.parameters.indexOf(p)
          val hasUnderscores   = ScUnderScoreSectionUtil.isUnderscoreFunction(fn)

          @tailrec
          def extractFromFunctionType(tpe: ScType, checkDeep: Boolean = false): Option[ScType] =
            tpe match {
              case functionLikeType(FunctionN, retTpe, _) if checkDeep =>
                extractFromFunctionType(retTpe)
              case functionLikeType(_, _, paramTpes) => paramTpes.lift(idx)
              case _                                 => None
            }

          eTpe.flatMap(extractFromFunctionType(_, hasUnderscores))
        case _ => None
      }
  }


// Expression has no expected type if followed by "." + "Identifier expected" error, #SCL-15754
  private def isInIncompeteCode(e: ScExpression): Boolean = {
    def isIncompleteDot(e1: LeafPsiElement, e2: PsiErrorElement) =
      e1.textMatches(".") && e2.getErrorDescription == "Identifier expected"

    e.nextSiblings.toSeq match {
      case Seq(e1: LeafPsiElement, e2: PsiErrorElement, _ @_*) if isIncompleteDot(e1, e2) => true
      case Seq(_: PsiWhiteSpace, e2: LeafPsiElement, e3: PsiErrorElement, _ @_*) if isIncompleteDot(e2, e3) => true
      case _ => false
    }
  }

  /**
   * @return (expectedType, expectedTypeElement)
   */
  def expectedExprTypes(expr: ScExpression, withResolvedFunction: Boolean = false,
                        fromUnderscore: Boolean = true): Array[ParameterType] = {
    import expr.projectContext

    if (isInIncompeteCode(expr)) {
      return Array.empty
    }

    val sameInContext = expr.getDeepSameElementInContext

    def fromFunction(tp: ParameterType): Array[ParameterType] = {
      val functionLikeType = FunctionLikeType(expr)
      tp._1 match {
        case functionLikeType(_, retTpe, _) => Array((retTpe, None))
        case _                              => Array.empty
      }
    }

    def mapResolves(resolves: Array[ScalaResolveResult], types: Array[TypeResult]): Array[(TypeResult, Boolean)] =
      resolves.zip(types).map {
        case (r, tp) => (tp, isApplyDynamicNamed(r))
      }

    def argIndex(argExprs: Seq[ScExpression]) =
      if (sameInContext == null) 0
      else argExprs.indexWhere(_ == sameInContext).max(0)

    def expectedTypesForArg(invocation: MethodInvocation, arg: ScExpression): Array[ParameterType] = {
      val argExprs = invocation.argumentExpressions

      val invoked = invocation.getEffectiveInvokedExpr
      val tps = invoked match {
        case ref: ScReferenceExpression =>
          if (!withResolvedFunction) mapResolves(ref.shapeResolve, ref.shapeMultiType)
          else mapResolves(ref.multiResolveScala(false), ref.multiType)
        case gen: ScGenericCall =>
          if (!withResolvedFunction) {
            val multiType = gen.shapeMultiType
            gen.shapeMultiResolve.map(mapResolves(_, multiType)).getOrElse(multiType.map((_, false)))
          } else {
            val multiType = gen.multiType
            gen.multiResolve.map(mapResolves(_, multiType)).getOrElse(multiType.map((_, false)))
          }
        case _ => Array((invoked.getNonValueType(), false))
      }
      val updatedWithExpected = tps.map {
        case (r, isDynamicNamed) => (r.map(invocation.updateAccordingToExpectedType), isDynamicNamed)
      }
      updatedWithExpected
        .filterNot(_._1.exists(_.equiv(Nothing)))
        .flatMap {
          case (r, isDynamicNamed) =>
            computeExpectedParamType(expr, r, argExprs, argIndex(argExprs), Some(invocation), isDynamicNamed = isDynamicNamed)
        }
    }

    val result: Array[ParameterType] = expr.getContext match {
      case p: ScParenthesisedExpr => p.expectedTypesEx(fromUnderscore = false)
      //see SLS[6.11]
      case b: ScBlockExpr => b.resultExpression match {
        case Some(e) if b.needCheckExpectedType && e == sameInContext => b.expectedTypesEx(fromUnderscore = true)
        case _ => Array.empty
      }
      //see SLS[6.16]
      case cond: ScIf if cond.condition.getOrElse(null: ScExpression) == sameInContext => Array((api.Boolean, None))
      case cond: ScIf if cond.elseExpression.isDefined => cond.expectedTypesEx(fromUnderscore = true)
      //see SLA[6.22]
      case tr@ScTry(Some(e), _, _) if e == expr =>
        tr.expectedTypesEx(fromUnderscore = true)
      case wh: ScWhile if wh.condition.getOrElse(null: ScExpression) == sameInContext => Array((api.Boolean, None))
      case _: ScWhile => Array((Unit, None))
      case d: ScDo if d.condition.getOrElse(null: ScExpression) == sameInContext => Array((api.Boolean, None))
      case _: ScDo => Array((api.Unit, None))
      case _: ScFinallyBlock => Array((api.Unit, None))
      case _: ScCatchBlock => Array.empty
      case te: ScThrow =>
        // Not in the SLS, but in the implementation.
        val throwableClass = ScalaPsiManager.instance(te.getProject).getCachedClass(te.resolveScope, "java.lang.Throwable")
        val throwableType = throwableClass.map(new ScDesignatorType(_)).getOrElse(Any)
        Array((throwableType, None))
      //see SLS[8.4]
      case c: ScCaseClause => c.getContext.getContext match {
        case m: ScMatch => m.expectedTypesEx(fromUnderscore = true)
        case b: ScBlockExpr if b.isInCatchBlock =>
          b.getContext.getContext.asInstanceOf[ScTry].expectedTypesEx(fromUnderscore = true)
        case b: ScBlockExpr if b.isAnonymousFunction =>
          b.expectedTypesEx(fromUnderscore = true).flatMap(tp => fromFunction(tp))
        case _ => Array.empty
      }
      //see SLS[6.23]
      case f: ScFunctionExpr => f.expectedTypesEx(fromUnderscore = true).flatMap(tp => fromFunction(tp))
      case t: ScTypedExpression if t.getLastChild.isInstanceOf[ScSequenceArg] =>
        t.expectedTypesEx(fromUnderscore = true)
      //SLS[6.13]
      case t: ScTypedExpression =>
        t.typeElement match {
          case Some(te) => Array((te.`type`().getOrAny, Some(te)))
          case _ => Array.empty
        }
      //SLS[6.15]
      case a: ScAssignment if a.rightExpression.getOrElse(null: ScExpression) == sameInContext =>
        a.leftExpression match {
          case ref: ScReferenceExpression if (!a.getContext.isInstanceOf[ScArgumentExprList] && !(
            a.getContext.isInstanceOf[ScInfixArgumentExpression] && a.getContext.asInstanceOf[ScInfixArgumentExpression].isCall)) ||
                  ref.qualifier.isDefined ||
                  ScUnderScoreSectionUtil.isUnderscore(expr) /* See SCL-3512, SCL-3525, SCL-4809, SCL-6785 */ =>
            ref.bind() match {
              case Some(ScalaResolveResult(named: PsiNamedElement, subst: ScSubstitutor)) =>
                ScalaPsiUtil.nameContext(named) match {
                  case v: ScValue =>
                    Array((subst(named.asInstanceOf[ScTypedDefinition].
                      `type`().getOrAny), v.typeElement))
                  case v: ScVariable =>
                    Array((subst(named.asInstanceOf[ScTypedDefinition].
                      `type`().getOrAny), v.typeElement))
                  case f: ScFunction if f.paramClauses.clauses.isEmpty =>
                    a.mirrorMethodCall match {
                      case Some(call) =>
                        call.args.exprs.head.expectedTypesEx(fromUnderscore = fromUnderscore)
                      case None => Array.empty
                    }
                  case p: ScParameter =>
                    //for named parameters
                    Array((subst(p.`type`().getOrAny), p.typeElement))
                  case f: PsiField =>
                    Array((subst(f.getType.toScType()), None))
                  case _ => Array.empty
                }
              case _ => Array.empty
            }
          case _: ScReferenceExpression => expectedExprTypes(a)
          case _: ScMethodCall =>
            a.mirrorMethodCall match {
              case Some(mirrorCall) => mirrorCall.args.exprs.last.expectedTypesEx(fromUnderscore = fromUnderscore)
              case _ => Array.empty
            }
          case _ => Array.empty
        }
      //method application
      case tuple: ScTuple if tuple.isCall =>
        expectedTypesForArg(tuple.getContext.asInstanceOf[ScInfixExpr], expr)
      case tuple: ScTuple =>
        val buffer = new ArrayBuffer[ParameterType]
        val exprs = tuple.exprs
        val index = exprs.indexOf(sameInContext)
        @tailrec
        def addType(aType: ScType): Unit = {
          aType match {
            case _: ScAbstractType => addType(aType.removeAbstracts)
            case TupleType(comps) if comps.length == exprs.length =>
              buffer += ((comps(index), None))
            case _ =>
          }
        }
        if (index >= 0) {
          for (tp: ScType <- tuple.expectedTypes(fromUnderscore = true)) addType(tp)
        }
        buffer.toArray
      case infix@ScInfixExpr.withAssoc(_, _, `sameInContext`) if !expr.isInstanceOf[ScTuple] =>
        val zExpr: ScExpression = expr match {
          case p: ScParenthesisedExpr => p.innerElement.getOrElse(return Array.empty)
          case _ => expr
        }
        expectedTypesForArg(infix, zExpr)
      //SLS[4.1]
      case v @ ScPatternDefinition.expr(`sameInContext`)  if v.isSimple => declaredOrInheritedType(v)
      case v @ ScVariableDefinition.expr(`sameInContext`) if v.isSimple => declaredOrInheritedType(v)
      //SLS[4.6]
      case v: ScFunctionDefinition if v.body.contains(sameInContext) => declaredOrInheritedType(v)
      //default parameters
      case param: ScParameter =>
        param.typeElement match {
          case Some(_) => Array((param.`type`().getOrAny, param.typeElement))
          case _ => Array.empty
        }
      case ret: ScReturn =>
        val fun: ScFunction = PsiTreeUtil.getContextOfType(ret, true, classOf[ScFunction])
        if (fun == null) return Array.empty
        fun.returnTypeElement match {
          case Some(rte: ScTypeElement) =>
            fun.returnType match {
              case Right(rt) => Array((rt, Some(rte)))
              case _ => Array.empty
            }
          case None => Array.empty
        }
      case args: ScArgumentExprList =>
        args.getContext match {
          case mc: ScMethodCall => expectedTypesForArg(mc, expr)
          case ctx @ (_: ScConstructorInvocation | _: ScSelfInvocation) =>
            val argExprs = args.exprs
            val argIdx = argIndex(argExprs)

            val tps = ctx match {
              case c: ScConstructorInvocation =>
                val clauseIdx = c.arguments.indexOf(args)

                if (!withResolvedFunction) c.shapeMultiType(clauseIdx)
                else c.multiType(clauseIdx)

              case s: ScSelfInvocation =>
                val clauseIdx = s.arguments.indexOf(args)

                if (!withResolvedFunction) s.shapeMultiType(clauseIdx)
                else s.multiType(clauseIdx)
            }

            tps.flatMap(computeExpectedParamType(expr, _, argExprs, argIdx))

          case _ =>
            Array.empty
        }
      case guard: ScGuard =>
        guard.desugared flatMap { _.content } match {
          case Some(content) => content.expectedTypesEx(fromUnderscore = fromUnderscore)
          case _ => Array.empty
        }
      case b: ScBlock if b.getContext.isInstanceOf[ScTry]
              || b.getContext.getContext.getContext.isInstanceOf[ScCatchBlock]
              || b.getContext.isInstanceOf[ScCaseClause]
              || b.getContext.isInstanceOf[ScFunctionExpr] => b.resultExpression match {
        case Some(e) if sameInContext == e => b.expectedTypesEx(fromUnderscore = true)
        case _ => Array.empty
      }
      case _ => Array.empty
    }

    @tailrec
    def checkIsUnderscore(expr: ScExpression): Boolean = {
      expr match {
        case p: ScParenthesisedExpr =>
          p.innerElement match {
            case Some(e) => checkIsUnderscore(e)
            case _ => false
          }
        case _ => ScUnderScoreSectionUtil.underscores(expr).nonEmpty
      }
    }

    if (fromUnderscore && checkIsUnderscore(expr)) {
      val res = new ArrayBuffer[ParameterType]
      for (tp <- result) {
        tp._1 match {
          case FunctionType(rt: ScType, _) => res += ((rt, None))
          case _ =>
        }
      }
      res.toArray
    } else result
  }

  private def computeExpectedParamType(expr: ScExpression,
                                       invokedExprType: TypeResult,
                                       argExprs: Seq[ScExpression],
                                       idx: Int,
                                       call: Option[MethodInvocation] = None,
                                       forApply: Boolean = false,
                                       isDynamicNamed: Boolean = false): Option[ParameterType] = {

    def fromMethodTypeParams(params: Seq[Parameter], subst: ScSubstitutor = ScSubstitutor.empty): Option[ParameterType] = {
      val newParams =
        if (subst.isEmpty) params
        else params.map(p => p.copy(paramType = subst(p.paramType)))

      val autoTupling = newParams.length == 1 && !newParams.head.isRepeated && argExprs.length > 1

      if (autoTupling) {
        newParams.head.paramType.removeAbstracts match {
          case TupleType(args) => paramTypeFromExpr(expr, paramsFromTuple(args), idx, isDynamicNamed)
          case _ => None
        }
      }
      else paramTypeFromExpr(expr, newParams, idx, isDynamicNamed)
    }

    //returns properly substituted method type of `apply` method invocation and whether it's apply dynamic named
    def tryApplyMethod(internalType: ScType, typeParams: Seq[TypeParameter]): Option[(TypeResult, Boolean)] = {
      call.getOrElse(expr).shapeResolveApplyMethod(internalType, argExprs, call) match {
        case Array(r@ScalaResolveResult(fun: ScFunction, s)) =>

          val polyType = fun.polymorphicType(s) match {
            case ScTypePolymorphicType(internal, params) =>
              ScTypePolymorphicType(internal, params ++ typeParams)
            case anotherType if typeParams.nonEmpty => ScTypePolymorphicType(anotherType, typeParams)
            case anotherType => anotherType
          }

          val applyMethodType = polyType
            .updateTypeOfDynamicCall(r.isDynamic)

          val updatedMethodCall = call.map(_.updateAccordingToExpectedType(applyMethodType))
            .getOrElse(applyMethodType)

          Some((Right(updatedMethodCall), isApplyDynamicNamed(r)))
        case _ =>
          None
      }
    }

    invokedExprType match {
      case Right(ScMethodType(_, params, _)) =>
        fromMethodTypeParams(params)
      case Right(t@ScTypePolymorphicType(ScMethodType(_, params, _), _)) =>
        val expectedType = call.flatMap(_.expectedType()).getOrElse(Any(expr))
        fromMethodTypeParams(params, t.argsProtoTypeSubst(expectedType))
      case Right(anotherType) if !forApply =>
        val (internalType, typeParams) = anotherType match {
          case ScTypePolymorphicType(internal, tps) => (internal, tps)
          case t => (t, Seq.empty)
        }
        tryApplyMethod(internalType, typeParams) match {
          case Some((applyInvokedType, isApplyDynamicNamed)) =>
            computeExpectedParamType(expr, applyInvokedType, argExprs, idx, forApply = true, isDynamicNamed = isApplyDynamicNamed)
          case _ => None
        }
      case _ => None
    }
  }

  private def paramTypeFromExpr(expr: ScExpression, params: Seq[Parameter], idx: Int, isDynamicNamed: Boolean): Option[ParameterType] = {
    import expr.elementScope

    def findByIdx(params: Seq[Parameter]): ParameterType = {
      def simple = (params(idx).paramType, typeElem(params(idx)))
      def repeated = (params.last.paramType, typeElem(params.last))

      if (idx >= params.length)
        if (params.nonEmpty && params.last.isRepeated) repeated
        else (Nothing, None)
      else simple
    }

    expr match {
      case assign: ScAssignment => Some {
        if (isDynamicNamed) paramTypeForDynamicNamed(findByIdx(params))
        else paramTypeForNamed(assign, params).getOrElse(findByIdx(params))
      }
      case typedStmt: ScTypedExpression if typedStmt.isSequenceArg && params.nonEmpty =>
        paramTypeForRepeated(params)
      case _ =>
        Some(findByIdx(params))
    }
  }

  private def typeElem(parameter: Parameter): Option[ScTypeElement] = parameter.paramInCode.flatMap(_.typeElement)

  private def paramTypeForDynamicNamed(original: ParameterType): ParameterType = {
    val (tp, te) = original
    tp.removeAbstracts match {
      case TupleType(comps) if comps.length == 2 =>
        val actualArg = (comps(1), te.map {
          case t: ScTupleTypeElement if t.components.length == 2 => t.components(1)
          case t => t
        })
        actualArg
      case _ => (tp, te)
    }
  }

  private def paramTypeForNamed(assign: ScAssignment, params: Seq[Parameter]): Option[ParameterType] = {
    val lE = assign.leftExpression
    lE match {
      case ref: ScReferenceExpression if ref.qualifier.isEmpty =>
        params
          .find(parameter => ScalaNamesUtil.equivalent(parameter.name, ref.refName))
          .map (param => (param.paramType, typeElem(param)))
      case _ => None
    }
  }

  private def paramTypeForRepeated(params: Seq[Parameter])(implicit elementScope: ElementScope): Option[ParameterType] = {
    val seqClass = elementScope.getCachedClass("scala.collection.Seq")
    seqClass.map { seq =>
      (ScParameterizedType(ScalaType.designator(seq), Seq(params.last.paramType)), None)
    }
  }

  private def paramsFromTuple(tupleArgs: Seq[ScType]): Seq[Parameter] = tupleArgs.zipWithIndex.map {
    case (tpe, index) => Parameter(tpe, isRepeated = false, index = index)
  }

  private def declaredOrInheritedType(member: ScMember): Array[ParameterType] = {
    import member.projectContext

    val declaredType = member match {
      case fun: ScFunctionDefinition if fun.returnTypeElement.isEmpty && !fun.hasAssign =>
        Some((api.Unit, None))
      case fun: ScFunction =>
        fun.returnTypeElement.flatMap(te => fun.returnType.toOption.map((_, Some(te))))
      case v: ScValueOrVariable =>
        v.typeElement.map(te => (te.`type`().getOrAny, Some(te)))
      case _ => return Array.empty
    }
    declaredType.orElse {
      inheritedType(member).map((_, None))
    }.toArray
  }

  private def inheritedType(member: ScMember): Option[ScType] = {
    import member.projectContext

    //is necessary to avoid recursion
    if (member.getParent.isInstanceOf[ScEarlyDefinitions])
      return None

    val typeParameters =
      member.asOptionOf[ScFunction].map(_.typeParameters).getOrElse(Seq.empty)

    val superMemberAndSubstitutor = member match {
      case fun: ScFunction => fun.superMethodAndSubstitutor
      case other: ScMember => valSuperSignature(other).map(s => (s.namedElement, s.substitutor))
    }
    superMemberAndSubstitutor match {
      case Some((fun: ScFunction, subst)) =>
        val typeParamSubst =
          ScSubstitutor.bind(fun.typeParameters, typeParameters)(TypeParameterType(_))

        fun.returnType.toOption.map(typeParamSubst.followed(subst))
      case Some((fun: ScSyntheticFunction, _)) =>
        val typeParamSubst =
          ScSubstitutor.bind(fun.typeParameters, typeParameters)(TypeParameterType(_))

        Some(typeParamSubst(fun.retType))
      case Some((fun: PsiMethod, subst)) =>
        val typeParamSubst =
          ScSubstitutor.bind(fun.getTypeParameters, typeParameters)(TypeParameterType(_))

        Some(typeParamSubst.followed(subst)(fun.getReturnType.toScType()))
      case Some((t: Typeable, s: ScSubstitutor)) =>
        t.`type`().map(s).toOption
      case _ => None
    }
  }

  private def valSuperSignature(m: ScMember): Option[TermSignature] = {

    //expected type for values is not inherited from empty-parens functions
    def isParameterless(s: TermSignature) = s.namedElement match {
      case f: ScFunction                       => f.isParameterless
      case m: PsiMethod                        => !m.hasParameters
      case _: ScClassParameter                 => true
      case inNameContext(_: ScValueOrVariable) => true
      case _                                   => false
    }

    def superSignature(name: String, containingClass: PsiClass) = {
      val sigs = TypeDefinitionMembers.getSignatures(containingClass).forName(name)
      sigs.nodesIterator.collectFirst {
        case node if node.info.paramLength == 0 =>
          node.primarySuper.map(_.info).filter(isParameterless)
      }.flatten
    }

    val maybeName = m match {
      case v: ScValueOrVariable => v.declaredNames.headOption
      case cp: ScClassParameter if cp.isClassMember => Some(cp.name)
      case _ => None
    }

    for {
      name <- maybeName
      containingClass <- m.containingClass.toOption
      signature <- superSignature(name, containingClass)
    } yield {
      signature
    }
  }

}

private object ExpectedTypesImpl {

  implicit class ScMethodCallEx(private val invocation: MethodInvocation) extends AnyVal {

    def updateAccordingToExpectedType(`type`: ScType): ScType =
      InferUtil.updateAccordingToExpectedType(`type`, filterTypeParams = false, invocation.expectedType(), invocation, canThrowSCE = false)
  }

  implicit class ScExpressionForExpectedTypesEx(private val expr: ScExpression) extends AnyVal {

    import expr.projectContext
    import org.jetbrains.plugins.scala.lang.psi.types.Compatibility.Expression._

    @CachedWithRecursionGuard(expr, Array.empty[ScalaResolveResult], ModCount.getBlockModificationCount)
    def shapeResolveApplyMethod(tp: ScType, exprs: Seq[ScExpression], call: Option[MethodInvocation]): Array[ScalaResolveResult] = {
      val applyProc =
        new MethodResolveProcessor(expr, "apply", List(exprs), Seq.empty, Seq.empty /* todo: ? */ ,
          StdKinds.methodsOnly, isShapeResolve = true)
      applyProc.processType(tp, expr, ScalaResolveState.withFromType(tp))
      var cand = applyProc.candidates
      if (cand.length == 0 && call.isDefined) {
        val expr = call.get.getEffectiveInvokedExpr

        ImplicitResolveResult.processImplicitConversions("apply", expr, applyProc, precalculatedType = Some(tp)) {
          identity
        }(expr)
        cand = applyProc.candidates
      }
      if (cand.length == 0 && conformsToDynamic(tp, expr.resolveScope) && call.isDefined) {
        cand = ScalaPsiUtil.processTypeForUpdateOrApplyCandidates(call.get, tp, isShape = true, isDynamic = true)
      }
      cand
    }
  }

}
