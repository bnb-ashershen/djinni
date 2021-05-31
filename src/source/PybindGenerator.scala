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

class PybindGenerator(spec: Spec) extends Generator(spec) {

  val marshal = new CppMarshal(spec)

  val writeCppFile = writeCppFileGeneric(spec.pybindOutFolder.get, "", spec.cppFileIdentStyle, spec.cppIncludePrefix) _
  val idPybind = IdentStyle.pythonDefault

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
      m match {
        case d: MDef => d.body match {
          case r: Record => cpp.add("#include " + marshal.include(d.name, r.ext.cpp))
          case e: Enum => cpp.add("#include " + marshal.include(d.name))
          case i: Interface => cpp.add("#include " + marshal.include(d.name))
        }
        case e: MExtern => cpp.add("#include " + e.cpp.header)
        case _ =>
      }
    }
  }

  def writePybindRefs(w: IndentWriter) {
    spec.pybindOverrideHeader match {
        case Some(overrideHeader) => w.wl("#include " + overrideHeader)
        case _ =>
    }
    w.wl
    w.wl("#include <pybind11/pybind11.h>")
    w.wl("#include <pybind11/stl.h>")
    w.wl("#include <pybind11/functional.h>")
    w.wl
    w.wl("namespace py = pybind11;")
    w.wl("using namespace " + spec.cppNamespace + ";")
    w.wl
  }

  override def generateEnum(origin: String, ident: Ident, doc: Doc, e: Enum) {
    val refs = new CppRefs(ident.name)
    val self = marshal.typename(ident, e)

    writeCppFile(ident, origin, refs.cpp, w => {
        writePybindRefs(w)
        w.w(s"void pybind11_init_$self(py::module& m)").braced {
            w.wl(s"py::enum_<$self>(m, "+q(idPybind.className(self))+", "+pydoc(doc)+")")
            w.increase()
            for (o <- normalEnumOptions(e)) {
                val name = o.ident.name
                w.wl(".value(" +q(idPybind.enum(name))+ s", $self::$name, " + pydoc(o.doc) + ")")
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
        writePybindRefs(w)
        val overrideDefine = "PYBIND_OVERRIDE_" + idPybind.const(self)
        w.wl(s"#ifndef $overrideDefine")
        w.wl(s"#define $overrideDefine")
        w.wl(s"#endif // $overrideDefine")
        w.wl
        w.w(s"void pybind11_init_$self(py::module& m)").braced {
            w.wl(s"py::class_<$self>(m, "+q(idPybind.className(self))+", "+pydoc(doc)+")")
            w.increase()

            // HACK: pybind doesn't support non-copyable objects
            val typeByValue = r.fields.exists(f => isRecordByValue(f.ty.resolved))
            w.w(if(typeByValue) "//" else "")

            val tys = r.fields.map(f => marshal.fieldType(f.ty)).mkString(", ")
            w.wl(s".def(py::init<$tys>())")
            for(f <- r.fields) {
                // HACK: pybind doesn't support non-copyable objects
                w.w(if (isRecordByValue(f.ty.resolved)) "//" else "")
                val d = if (isRecordByValue(f.ty.resolved)) Doc(Seq()) else f.doc

                val name = f.ident.name
                w.wl(".def_readwrite(" + q(idPybind.field(name)) + s", &$self::$name, " + pydoc(d) + ")")
            }
            w.wl(overrideDefine)
            w.wl(";")
            w.decrease()
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
        writePybindRefs(w)
        val overrideDefine = "PYBIND_OVERRIDE_" + idPybind.const(self)
        w.wl(s"#ifndef $overrideDefine")
        w.wl(s"#define $overrideDefine")
        w.wl(s"#endif // $overrideDefine")
        w.wl
        w.w(s"void pybind11_init_$self(py::module& m)").braced {
            w.wl(s"py::class_<$self, std::shared_ptr<$self>>(m, "+q(idPybind.className(self))+", "+pydoc(doc)+")")
            w.increase()
            for(m <- i.methods) {
                // HACK: pybind doesn't support non-copyable objects passing by value
                val paramByValue = m.params.exists(p => isRecordByValue(p.ty.resolved))
                val retByValue = m.ret match {
                    case Some(ty) => isRecordByValue(ty.resolved)
                    case _ => false
                }
                val commentUnsupportedMethod = if(paramByValue || retByValue) "//" else ""
                w.w(commentUnsupportedMethod)
                val d = if(paramByValue || retByValue) Doc(Seq()) else m.doc

                val name = m.ident.name
                w.wl(".def(" + q(idPybind.method(name)) + s", &$self::$name, " + pydoc(d) + ")")
            }
            w.wl(overrideDefine)
            w.wl(";")
            w.decrease()
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

  def pydoc(doc: Doc): String = doc.lines.length match {
    case 0 => q("")
    case 1 => "R" + q("pydoc(" + doc.lines.head + ")pydoc")
    case _ => "R" + q("pydoc(\n" + doc.lines.mkString("\n") + "\n)pydoc")
  }
}
