package org.jetbrains.plugins.scala.lang.psi

import com.intellij.extapi.psi.PsiFileBase
import com.intellij.lang.Language
import com.intellij.psi._
import com.intellij.psi.scope.PsiScopeProcessor
import org.jetbrains.plugins.scala.ScalaFileType
import com.intellij.psi.tree.TokenSet
import org.jetbrains.annotations.Nullable
import org.jetbrains.plugins.scala.icons.Icons
import com.intellij.lang.ASTNode
import com.intellij.psi.tree.IElementType
import org.jetbrains.plugins.scala.lang.parser.ScalaElementTypes
import psi.api.toplevel._
import psi.api.toplevel.typedef._
import psi.api.toplevel.packaging._
import org.jetbrains.plugins.scala.lang.psi.api.toplevel.typedef._
import org.jetbrains.plugins.scala.lang.psi.api.base.ScStableCodeReferenceElement

import _root_.scala.collection.mutable._


class ScalaFile (viewProvider: FileViewProvider) extends PsiFileBase (viewProvider, ScalaFileType.SCALA_FILE_TYPE.getLanguage())
with ScalaPsiElement with ScTypeDefinitionOwner with PsiClassOwner with ScDeclarationSequenceHolder {

  override def getViewProvider = viewProvider
  override def getFileType = ScalaFileType.SCALA_FILE_TYPE
  override def toString = "ScalaFile"

  def setPackageName(name: String) = {
    //todo
  }

  def getPackagings = findChildrenByClass(classOf[ScPackaging])

  def getPackageName =
    packageStatement match {
      case None => ""
      case Some(stat) => stat.getPackageName
    }

  def packageStatement = findChild(classOf[ScPackageStatement])

  override def getClasses = getTypeDefinitionsArray.map(t => t.asInstanceOf[PsiClass])

  def getTopStatements: Array[ScTopStatement] = findChildrenByClass(classOf[ScTopStatement])

  override def getTypeDefinitions(): Seq[ScTypeDefinition] = findChildrenByClass(classOf[ScTypeDefinition])

  def icon = Icons.FILE_TYPE_LOGO

  override def processDeclarations(processor: PsiScopeProcessor,
      state : ResolveState,
      lastParent: PsiElement,
      place: PsiElement): Boolean = {
    import org.jetbrains.plugins.scala.lang.resolve._
    if (!super[ScDeclarationSequenceHolder].processDeclarations(processor,
          state, lastParent, place)) return false

    place match {
      case ref : ScStableCodeReferenceElement if ref.refName == "_root_" => {
        val top = JavaPsiFacade.getInstance(getProject()).findPackage("")
        if (top != null && !processor.execute(top, state.put(ResolverEnv.nameKey, "_root_"))) return false
        state.put(ResolverEnv.nameKey, null)
      }
      case _ => {
        var curr = JavaPsiFacade.getInstance(getProject()).findPackage(getPackageName)
        while (curr != null) {
          if (!curr.processDeclarations(processor, state, null, place)) return false
          curr = curr.getParentPackage
        }
      }
    }

    for (implP <- ImplicitlyImported.packages) {
      val pack = JavaPsiFacade.getInstance(getProject()).findPackage(implP)
      if (pack != null && !pack.processDeclarations(processor, state, null, place)) return false
    }

    for (implObj <- ImplicitlyImported.objects) {
      val clazz = JavaPsiFacade.getInstance(getProject()).findClass(implObj, getResolveScope)
      if (clazz != null && !clazz.processDeclarations(processor, state, null, place)) return false
    }

    true
  }
}

object ImplicitlyImported {
  val packages = Array("java.lang", "scala")
  val objects = Array("scala.Predef")
}
