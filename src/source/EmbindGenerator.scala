/**
  * Copyright 2014 Dropbox, Inc.
  *
  * Licensed under the Apache License, Version 2.0 (the "License");
  * you may not use this file except in compliance with the License.
  * You may obtain a copy of the License at
  *
  *    http://www.apache.org/licenses/LICENSE-2.0
  *
  * Unless required by applicable law or agreed to in writing, software
  * distributed under the License is distributed on an "AS IS" BASIS,
  * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  * See the License for the specific language governing permissions and
  * limitations under the License.
  */

package djinni

import djinni.ast.Record.DerivingType
import djinni.ast._
import djinni.generatorTools._
import djinni.meta._
import djinni.writer.IndentWriter

import scala.collection.mutable

class EmbindGenerator(spec: Spec) extends Generator(spec) {

  val marshal = new CppMarshal(spec)

  val writeCppFile = writeCppFileGeneric(spec.embindOutFolder.get, "", spec.cppFileIdentStyle, spec.cppIncludePrefix) _
  val idEmbind = IdentStyle.javaDefault

  class CppRefs(name: String) {
    var hpp = mutable.TreeSet[String]()
    var hppFwds = mutable.TreeSet[String]()
    var cpp = mutable.TreeSet[String]()

    def find(ty: TypeRef, forwardDeclareOnly: Boolean) { find(ty.resolved, forwardDeclareOnly) }
    def find(tm: MExpr, forwardDeclareOnly: Boolean) {
      tm.args.foreach((x) => find(x, forwardDeclareOnly))
      find(tm.base, forwardDeclareOnly)
    }
    def find(m: Meta, forwardDeclareOnly : Boolean) = {
      for(r <- marshal.hppReferences(m, name, forwardDeclareOnly)) r match {
        case ImportRef(arg) => hpp.add("#include " + arg)
        case DeclRef(decl, Some(spec.cppNamespace)) => hppFwds.add(decl)
        case DeclRef(_, _) =>
      }
      for(r <- marshal.cppReferences(m, name, forwardDeclareOnly)) r match {
        case ImportRef(arg) => cpp.add("#include " + arg)
        case DeclRef(_, _) =>
      }
    }
  }

  def writeEmbindRefs(w: IndentWriter) {
    spec.embindOverrideHeader match {
        case Some(overrideHeader) => w.wl("#include " + overrideHeader)
        case _ =>
    }
    w.wl
    w.wl("#include <emscripten/bind.h>")
    w.wl("#include <emscripten/val.h>")
    w.wl
    w.wl("using namespace emscripten;")
    w.wl("using namespace " + spec.cppNamespace + ";")
    w.wl
  }

  override def generateEnum(origin: String, ident: Ident, doc: Doc, e: Enum) {
    val refs = new CppRefs(ident.name)
    val self = marshal.typename(ident, e)

    writeCppFile(ident, origin, refs.cpp, w => {
        writeEmbindRefs(w)
        w.w(s"EMSCRIPTEN_BINDINGS($self)").braced {
            w.wl(s"enum_<$self>("+q(idEmbind.ty(self))+")")
            w.increase()
            for (o <- normalEnumOptions(e)) {
                val name = o.ident.name
                w.wl(".value(" +q(idEmbind.enum(name))+ s", $self::$name)")
            }
            w.wl(";")
            w.decrease()
        }
    })
  }

  override def generateRecord(origin: String, ident: Ident, doc: Doc, params: Seq[TypeParam], r: Record) {
    val refs = new CppRefs(ident.name)
    val self = marshal.typename(ident, r)

    r.fields.foreach(f => refs.find(f.ty, false))
    //r.consts.foreach(c => refs.find(c.ty, false))

    writeCppFile(ident, origin, refs.cpp, w => {
        writeEmbindRefs(w)
        val overrideDefine = "EMBIND_OVERRIDE_" + idEmbind.enum(self)
        w.wl(s"#ifndef $overrideDefine")
        w.wl(s"#define $overrideDefine")
        w.wl(s"#endif // $overrideDefine")
        w.wl
        w.w(s"EMSCRIPTEN_BINDINGS($self)").braced {
            w.wl(s"class_<$self>("+q(idEmbind.ty(self))+")")
            w.increase()

            // HACK: embind doesn't support non-copyable objects
            val typeByValue = r.fields.exists(f => isRecordByValue(f.ty.resolved))
            w.w(if(typeByValue) "//" else "")

            val tys = r.fields.map(f => marshal.fieldType(f.ty)).mkString(", ")
            w.wl(s".constructor<$tys>()")
            for(f <- r.fields) {
                // HACK: embind doesn't support non-copyable objects
                w.w(if (isRecordByValue(f.ty.resolved)) "//" else "")

                val name = f.ident.name
                w.wl(".property(" + q(idEmbind.field(name)) + s", &$self::$name)")
            }
            w.wl(overrideDefine)
            w.wl(";")
            w.decrease()

            // HACK: embind doesn't support non-copyable objects
            w.w(if(typeByValue) "//" else "")

            w.wl(s"register_vector<$self>(" + q("Vector" + idEmbind.ty(self)) + ");")
        }
    })
  }

  override def generateInterface(origin: String, ident: Ident, doc: Doc, typeParams: Seq[TypeParam], i: Interface) {
    val refs = new CppRefs(ident.name)
    val self = marshal.typename(ident, i)

    i.methods.map(m => {
      m.params.map(p => refs.find(p.ty, true))
      m.ret.foreach(x => refs.find(x, true))
    })
    // i.consts.map(c => {
    //   refs.find(c.ty, true)
    // })

    writeCppFile(ident, origin, refs.cpp, w => {
        writeEmbindRefs(w)
        val overrideDefine = "EMBIND_OVERRIDE_" + idEmbind.enum(self)
        w.wl(s"#ifndef $overrideDefine")
        w.wl(s"#define $overrideDefine")
        w.wl(s"#endif // $overrideDefine")
        w.wl
        w.w(s"EMSCRIPTEN_BINDINGS($self)").braced {
            w.wl(s"class_<$self>("+q(idEmbind.ty(self))+")")
            w.increase()
            for(m <- i.methods) {
                // HACK: embind doesn't support non-copyable objects passing by value
                val paramByValue = m.params.exists(p => isRecordByValue(p.ty.resolved))
                val retByValue = m.ret match {
                    case Some(ty) => isRecordByValue(ty.resolved)
                    case _ => false
                }
                val commentUnsupportedMethod = if(paramByValue || retByValue) "//" else ""
                w.w(commentUnsupportedMethod)

                val name = m.ident.name
                if (m.static) {
                    w.wl(".class_function(" + q(idEmbind.method(name)) + s", &$self::$name)")
                } else {
                    w.wl(".function(" + q(idEmbind.method(name)) + s", &$self::$name, pure_virtual())")
                }
            }
            w.wl(s".smart_ptr<std::shared_ptr<$self>>(" + q("SharedPtr" + idEmbind.ty(self)) + ")")
            w.wl(overrideDefine)
            w.wl(";")
            w.decrease()
            w.wl(s"register_vector<std::shared_ptr<$self>>(" + q("Vector" + idEmbind.ty(self)) + ");")
        }
    })
  }

  def isRecordByValue(tm: MExpr): Boolean = tm.base match {
    case e: MExtern => e.defType match {
      case DRecord => e.cpp.byValue
      case _ => false
    }
    case MOptional => isRecordByValue(tm.args.head)
    case _ => false
  }
}
