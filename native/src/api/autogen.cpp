// Claricpp API

#include "headers.hpp"
#include "manual.hpp"
#include <algorithm>
#include <cstddef>
#include <functional>
#include <ios>
#include <iterator>
#include <locale>
#include <map>
#include <memory>
#include <optional>
#include <ostream>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include <stack>
#include <stdexcept>
#include <streambuf>
#include <string>
#include <utility>
#include <variant>
#include <vector>
#include <z3++.h>


//
// Derived from file: binder/raw_output/clari.cpp
//


/** The name of the root module */
CCSC API::root_mod_name {"clari"};

namespace API::Binder {

typedef std::function< pybind11::module & (std::string const &) > ModuleGetter;

void bind_unknown_unknown(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_1(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_2(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_3(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_4(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_5(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_6(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_7(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_8(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_9(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_10(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_11(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_12(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_13(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_14(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_15(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_16(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_17(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_18(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_19(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_20(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_21(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_22(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_23(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_24(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_25(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_26(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_27(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_28(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_29(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_30(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_31(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_32(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_33(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_34(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_35(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_36(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_37(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_38(std::function< pybind11::module &(std::string const &namespace_) > &M);
void bind_unknown_unknown_39(std::function< pybind11::module &(std::string const &namespace_) > &M);

} // namespace API::Binder


PYBIND11_MODULE(clari, root_module) {
	root_module.doc() = "clari module";

	std::map <std::string, pybind11::module> modules;
	API::Binder::ModuleGetter M = [&](std::string const &namespace_) -> pybind11::module & {
		auto it = modules.find(namespace_);
		if( it == modules.end() ) throw std::runtime_error("Attempt to access pybind11::module for namespace " + namespace_ + " before it was created!!!");
		return it->second;
	};

	modules[""] = root_module;

	static std::vector<std::string> const reserved_python_words {"nonlocal", "global", };

	auto mangle_namespace_name(
		[](std::string const &ns) -> std::string {
			if ( std::find(reserved_python_words.begin(), reserved_python_words.end(), ns) == reserved_python_words.end() ) return ns;
			else return ns+'_';
		}
	);

	std::vector< std::pair<std::string, std::string> > sub_modules {
		{"", "Backend"},
		{"Backend", "Z3"},
		{"", "CUID"},
		{"", "Create"},
		{"Create", "FP"},
		{"Create", "String"},
		{"", "Expr"},
		{"", "Factory"},
		{"", "Hash"},
		{"Hash", "Private"},
		{"", "Mode"},
		{"Mode", "FP"},
		{"Mode", "Sign"},
		{"", "Op"},
		{"Op", "FP"},
		{"Op", "String"},
		{"", "PyObj"},
		{"", "Util"},
		{"Util", "Backtrace"},
		{"Util", "Err"},
		{"", "API"},
	};
	for(auto &p : sub_modules ) modules[p.first.size() ? p.first+"::"+p.second : p.second] = modules[p.first].def_submodule( mangle_namespace_name(p.second).c_str(), ("Bindings for " + p.first + "::" + p.second + " namespace").c_str() );

	//pybind11::class_<std::shared_ptr<void>>(M(""), "_encapsulated_data_");

	API::Binder::bind_unknown_unknown(M);
	API::Binder::bind_unknown_unknown_1(M);
	API::Binder::bind_unknown_unknown_2(M);
	API::Binder::bind_unknown_unknown_3(M);
	API::Binder::bind_unknown_unknown_4(M);
	API::Binder::bind_unknown_unknown_5(M);
	API::Binder::bind_unknown_unknown_6(M);
	API::Binder::bind_unknown_unknown_7(M);
	API::Binder::bind_unknown_unknown_8(M);
	API::Binder::bind_unknown_unknown_9(M);
	API::Binder::bind_unknown_unknown_10(M);
	API::Binder::bind_unknown_unknown_11(M);
	API::Binder::bind_unknown_unknown_12(M);
	API::Binder::bind_unknown_unknown_13(M);
	API::Binder::bind_unknown_unknown_14(M);
	API::Binder::bind_unknown_unknown_15(M);
	API::Binder::bind_unknown_unknown_16(M);
	API::Binder::bind_unknown_unknown_17(M);
	API::Binder::bind_unknown_unknown_18(M);
	API::Binder::bind_unknown_unknown_19(M);
	API::Binder::bind_unknown_unknown_20(M);
	API::Binder::bind_unknown_unknown_21(M);
	API::Binder::bind_unknown_unknown_22(M);
	API::Binder::bind_unknown_unknown_23(M);
	API::Binder::bind_unknown_unknown_24(M);
	API::Binder::bind_unknown_unknown_25(M);
	API::Binder::bind_unknown_unknown_26(M);
	API::Binder::bind_unknown_unknown_27(M);
	API::Binder::bind_unknown_unknown_28(M);
	API::Binder::bind_unknown_unknown_29(M);
	API::Binder::bind_unknown_unknown_30(M);
	API::Binder::bind_unknown_unknown_31(M);
	API::Binder::bind_unknown_unknown_32(M);
	API::Binder::bind_unknown_unknown_33(M);
	API::Binder::bind_unknown_unknown_34(M);
	API::Binder::bind_unknown_unknown_35(M);
	API::Binder::bind_unknown_unknown_36(M);
	API::Binder::bind_unknown_unknown_37(M);
	API::Binder::bind_unknown_unknown_38(M);
	API::Binder::bind_unknown_unknown_39(M);

	// Manual API call
	API::bind_manual(root_module, M);
}


//
// File: binder/raw_output/unknown/unknown.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	{ // Util::Backtrace::Lazy file: line:21
		pybind11::class_<Util::Backtrace::Lazy, std::shared_ptr<Util::Backtrace::Lazy>> cl(M("Util::Backtrace"), "Lazy", "The lazy backtrace holder type " );
		cl.def("str", (std::string (Util::Backtrace::Lazy::*)() const) &Util::Backtrace::Lazy::str, "As string \n\nC++: Util::Backtrace::Lazy::str() const --> std::string");
	}
}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_1.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

// Util::Err::Claricpp file: line:35
struct PyCallBack_Util_Err_Claricpp : public Util::Err::Claricpp {
	using Util::Err::Claricpp::Claricpp;

};

namespace API::Binder {
void bind_unknown_unknown_1(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	{ // Util::Err::Claricpp file: line:35
		pybind11::class_<Util::Err::Claricpp, std::shared_ptr<Util::Err::Claricpp>, PyCallBack_Util_Err_Claricpp> cl(M("Util::Err"), "Claricpp", "The base claricpp exception class\n  Any exception thrown intentionally must subclass this\n  Note: Since exceptions do not need to be super fast and since we have const date members:\n  for clarity we ignore the rule of 5 in favor of what the compiler defaults. Subclasses\n  of Claricpp should feel free to do the same unless they have non-const data members\n  This class saves the last n_backtraces backtraces" );
		cl.def_static("log_atomic_change", (void (*)(const char *const, const bool, const bool)) &Util::Err::Claricpp::log_atomic_change, "Logs that an atomic was toggled \n\nC++: Util::Err::Claricpp::log_atomic_change(const char *const, const bool, const bool) --> void", pybind11::arg("what"), pybind11::arg("old"), pybind11::arg("new_"));
		cl.def_static("warn_backtrace_slow", (void (*)()) &Util::Err::Claricpp::warn_backtrace_slow, "Warns that enabling backtraces causes a performance hit \n\nC++: Util::Err::Claricpp::warn_backtrace_slow() --> void");
		cl.def_static("toggle_backtrace", [](const bool & a0) -> bool { return Util::Err::Claricpp::toggle_backtrace(a0); }, "", pybind11::arg("set"));
		cl.def_static("toggle_backtrace", (bool (*)(const bool, const bool)) &Util::Err::Claricpp::toggle_backtrace, "Enable / disable backtraces\n  Returns the old state\n\nC++: Util::Err::Claricpp::toggle_backtrace(const bool, const bool) --> bool", pybind11::arg("set"), pybind11::arg("log_me"));
		cl.def_static("backtraces_enabled", (bool (*)()) &Util::Err::Claricpp::backtraces_enabled, "Return true if and only if backtraces are enabled \n\nC++: Util::Err::Claricpp::backtraces_enabled() --> bool");
		cl.def("what", (const char * (Util::Err::Claricpp::*)() const) &Util::Err::Claricpp::what, "Message getter \n\nC++: Util::Err::Claricpp::what() const --> const char *", pybind11::return_value_policy::automatic);
		cl.def_static("lazy_backtrace", []() -> std::shared_ptr<const class Util::Backtrace::Lazy> { return Util::Err::Claricpp::lazy_backtrace(); }, "");
		cl.def_static("lazy_backtrace", (class std::shared_ptr<const class Util::Backtrace::Lazy> (*)(const unsigned long)) &Util::Err::Claricpp::lazy_backtrace, "Get a previous backtrace in an unevaluated form; returns {} on error\n  Get the a previous backtrace\n  Ignores the last index'th backtraces\n  Ex. index = 0 gets the last backtrace, index = 1 gets the second to last\n  Call ->str() on the result to get the backtrace as a string\n\nC++: Util::Err::Claricpp::lazy_backtrace(const unsigned long) --> class std::shared_ptr<const class Util::Backtrace::Lazy>", pybind11::arg("index"));
		cl.def_static("backtrace", []() -> std::string { return Util::Err::Claricpp::backtrace(); }, "");
		cl.def_static("backtrace", (std::string (*)(const unsigned long)) &Util::Err::Claricpp::backtrace, "Eagerly evaluated lazy_backtrace(index)\n  If lazy_backtrace(index) returns nullptr; will return {}\n  Unlike lazy_backtrace, this may throw if evaluation fails\n\nC++: Util::Err::Claricpp::backtrace(const unsigned long) --> std::string", pybind11::arg("index"));
	}
}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_10.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_10(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	{ // Factory::FactoryMade file: line:43
		pybind11::class_<Factory::FactoryMade, Factory::FactoryMade*, Hash::Hashed, CUID::HasCUID> cl(M("Factory"), "FactoryMade", "A type that can be constructed by the factory\n  All factory constructable types must subclass this\n  All subclasses that are or have an instantiable subclass constructed via factory\n	  1. Must include the FACTORY_ENABLE_CONSTRUCTION_FROM_BASE method. Note that\n		 this also defines a static_cuid\n  Warning: No virtual destructor; do *not* delete by base class pointer; avoid slicing!" );
	}
}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_11.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_11(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	{ // HasRepr file: line:16
		pybind11::class_<HasRepr<Expr::Base>, HasRepr<Expr::Base>*> cl(M(""), "HasRepr_Expr_Base_t", "" );
		cl.def("__repr__", (std::string (HasRepr<Expr::Base>::*)() const) &HasRepr<Expr::Base>::__repr__, "C++: HasRepr<Expr::Base>::__repr__() const --> std::string");
	}
	{ // HasRepr file: line:16
		pybind11::class_<HasRepr<PyObj::Base>, HasRepr<PyObj::Base>*> cl(M(""), "HasRepr_PyObj_Base_t", "" );
		cl.def("__repr__", (std::string (HasRepr<PyObj::Base>::*)() const) &HasRepr<PyObj::Base>::__repr__, "C++: HasRepr<PyObj::Base>::__repr__() const --> std::string");
	}
	{ // HasRepr file: line:16
		pybind11::class_<HasRepr<Op::Base>, HasRepr<Op::Base>*> cl(M(""), "HasRepr_Op_Base_t", "" );
		cl.def("__repr__", (std::string (HasRepr<Op::Base>::*)() const) &HasRepr<Op::Base>::__repr__, "C++: HasRepr<Op::Base>::__repr__() const --> std::string");
	}
}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_12.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

// Expr::Base file: line:32
struct PyCallBack_Expr_Base : public Expr::Base {
	using Expr::Base::Base;

	const char * type_name() const throw() override {
		pybind11::gil_scoped_acquire gil;
		pybind11::function overload = pybind11::get_overload(static_cast<const Expr::Base *>(this), "type_name");
		if (overload) {
			auto o = overload.operator()<pybind11::return_value_policy::reference>();
			if (pybind11::detail::cast_is_temporary_value_reference<const char *>::value) {
				static pybind11::detail::override_caster_t<const char *> caster;
				return pybind11::detail::cast_ref<const char *>(std::move(o), caster);
			}
			else return pybind11::detail::cast_safe<const char *>(std::move(o));
		}
		pybind11::pybind11_fail("Tried to call pure virtual function \"Base::type_name\"");
	}
};

namespace API::Binder {
void bind_unknown_unknown_12(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	{ // Expr::Base file: line:32
		pybind11::class_<Expr::Base, Expr::Base*, PyCallBack_Expr_Base, HasRepr<Expr::Base>, Factory::FactoryMade> cl(M("Expr"), "Base", "The base Expr type\n  All Exprs must subclass this" );
		cl.def_readonly("symbolic", &Expr::Base::symbolic);
		cl.def_readonly("op", &Expr::Base::op);
		cl.def_readonly("dict", &Expr::Base::dict);
		cl.def("type_name", (const char * (Expr::Base::*)() const) &Expr::Base::type_name, "Get the type name \n\nC++: Expr::Base::type_name() const --> const char *", pybind11::return_value_policy::automatic);
		cl.def("annotations", (class std::optional<class pybind11::dict> (Expr::Base::*)() const) &Expr::Base::annotations, "Get annotations\n  Warning: Do not edit this dict\n  pybind11 doesn't really do const, so we can't here either :(\n\nC++: Expr::Base::annotations() const --> class std::optional<class pybind11::dict>");
	}
}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_13.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_13(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	{ // BitLength file: line:12
		pybind11::class_<BitLength, BitLength*> cl(M(""), "BitLength", "A class with a const bit length " );
		cl.def_readonly("bit_length", &BitLength::bit_length);
	}
}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_14.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

// Expr::Bits file: line:16
struct PyCallBack_Expr_Bits : public Expr::Bits {
	using Expr::Bits::Bits;

	const char * type_name() const throw() override {
		pybind11::gil_scoped_acquire gil;
		pybind11::function overload = pybind11::get_overload(static_cast<const Expr::Bits *>(this), "type_name");
		if (overload) {
			auto o = overload.operator()<pybind11::return_value_policy::reference>();
			if (pybind11::detail::cast_is_temporary_value_reference<const char *>::value) {
				static pybind11::detail::override_caster_t<const char *> caster;
				return pybind11::detail::cast_ref<const char *>(std::move(o), caster);
			}
			else return pybind11::detail::cast_safe<const char *>(std::move(o));
		}
		pybind11::pybind11_fail("Tried to call pure virtual function \"Base::type_name\"");
	}
};

namespace API::Binder {
void bind_unknown_unknown_14(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	{ // Expr::Bits file: line:16
		pybind11::class_<Expr::Bits, Expr::Bits*, PyCallBack_Expr_Bits, Expr::Base, BitLength> cl(M("Expr"), "Bits", "This class represents an Expr of Bits " );
	}
	// Expr::bit_length(const class Expr::Base *const) file: line:40
	M("Expr").def("bit_length", (unsigned long long (*)(const class Expr::Base *const)) &Expr::bit_length, "Static casts T to Expr::Bits' raw pointer, then returns the bit_length\n  p may not be nullptr\n  Warning: This static casts, the user must ensure that p is a Bits\n\nC++: Expr::bit_length(const class Expr::Base *const) --> unsigned long long", pybind11::arg("p"));

	// Expr::bit_length(const class std::shared_ptr<const class Expr::Base> &) file: line:50
	M("Expr").def("bit_length", (unsigned long long (*)(const class std::shared_ptr<const class Expr::Base> &)) &Expr::bit_length, "Static casts T to Expr::Bits, then returns the bit_length\n  p may not be nullptr\n  Warning: This static casts, the user must ensure that p.get() is a Bits\n\nC++: Expr::bit_length(const class std::shared_ptr<const class Expr::Base> &) --> unsigned long long", pybind11::arg("p"));

}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_15.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_15(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	// Expr::are_same_type(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &) file: line:19
	M("Expr").def("are_same_type", (bool (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &)) &Expr::are_same_type<true>, "C++: Expr::are_same_type(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &) --> bool", pybind11::arg("x"), pybind11::arg("y"));

	// Expr::are_same_type(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &) file: line:19
	M("Expr").def("are_same_type", (bool (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &)) &Expr::are_same_type<false>, "C++: Expr::are_same_type(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &) --> bool", pybind11::arg("x"), pybind11::arg("y"));

	{ // Expr::Bool file: line:34
		pybind11::class_<Expr::Bool, std::shared_ptr<Expr::Bool>, Expr::Base> cl(M("Expr"), "Bool", "" );
		cl.def("type_name", (const char * (Expr::Bool::*)() const) &Expr::Bool::type_name, "C++: Expr::Bool::type_name() const --> const char *", pybind11::return_value_policy::automatic);
	}
	{ // Expr::String file: line:35
		pybind11::class_<Expr::String, std::shared_ptr<Expr::String>, Expr::Bits> cl(M("Expr"), "String", "" );
		cl.def("type_name", (const char * (Expr::String::*)() const) &Expr::String::type_name, "C++: Expr::String::type_name() const --> const char *", pybind11::return_value_policy::automatic);
	}
	{ // Expr::VS file: line:36
		pybind11::class_<Expr::VS, std::shared_ptr<Expr::VS>, Expr::Bits> cl(M("Expr"), "VS", "" );
		cl.def("type_name", (const char * (Expr::VS::*)() const) &Expr::VS::type_name, "C++: Expr::VS::type_name() const --> const char *", pybind11::return_value_policy::automatic);
	}
	{ // Expr::BV file: line:37
		pybind11::class_<Expr::BV, std::shared_ptr<Expr::BV>, Expr::Bits> cl(M("Expr"), "BV", "" );
		cl.def("type_name", (const char * (Expr::BV::*)() const) &Expr::BV::type_name, "C++: Expr::BV::type_name() const --> const char *", pybind11::return_value_policy::automatic);
	}
	{ // Expr::FP file: line:38
		pybind11::class_<Expr::FP, std::shared_ptr<Expr::FP>, Expr::Bits> cl(M("Expr"), "FP", "" );
		cl.def("type_name", (const char * (Expr::FP::*)() const) &Expr::FP::type_name, "C++: Expr::FP::type_name() const --> const char *", pybind11::return_value_policy::automatic);
	}
	// Expr::find(const unsigned long long) file: line:59
	M("Expr").def("find", (class std::shared_ptr<const class Expr::Base> (*)(const unsigned long long)) &Expr::find, "Get a shared pointer from a hash\n  If the object does not exist it returns a shared pointer to nullptr\n\nC++: Expr::find(const unsigned long long) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("h"));

}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_16.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_16(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	{ // Expr::TypeNames file: line:25
		pybind11::class_<Expr::TypeNames<Expr::FP>, std::shared_ptr<Expr::TypeNames<Expr::FP>>> cl(M("Expr"), "TypeNames_Expr_FP_t", "" );
		cl.def( pybind11::init( [](){ return new Expr::TypeNames<Expr::FP>(); } ) );
		cl.def( pybind11::init( [](Expr::TypeNames<Expr::FP> const &o){ return new Expr::TypeNames<Expr::FP>(o); } ) );
		cl.def("__call__", (const std::string & (Expr::TypeNames<Expr::FP>::*)() const) &Expr::TypeNames<Expr::FP>::operator(), "C++: Expr::TypeNames<Expr::FP>::operator()() const --> const std::string &", pybind11::return_value_policy::automatic);
	}
	{ // Expr::TypeNames file: line:25
		pybind11::class_<Expr::TypeNames<Expr::BV>, std::shared_ptr<Expr::TypeNames<Expr::BV>>> cl(M("Expr"), "TypeNames_Expr_BV_t", "" );
		cl.def( pybind11::init( [](){ return new Expr::TypeNames<Expr::BV>(); } ) );
		cl.def( pybind11::init( [](Expr::TypeNames<Expr::BV> const &o){ return new Expr::TypeNames<Expr::BV>(o); } ) );
		cl.def("__call__", (const std::string & (Expr::TypeNames<Expr::BV>::*)() const) &Expr::TypeNames<Expr::BV>::operator(), "C++: Expr::TypeNames<Expr::BV>::operator()() const --> const std::string &", pybind11::return_value_policy::automatic);
	}
	{ // Expr::TypeNames file: line:25
		pybind11::class_<Expr::TypeNames<Expr::String>, std::shared_ptr<Expr::TypeNames<Expr::String>>> cl(M("Expr"), "TypeNames_Expr_String_t", "" );
		cl.def( pybind11::init( [](){ return new Expr::TypeNames<Expr::String>(); } ) );
		cl.def( pybind11::init( [](Expr::TypeNames<Expr::String> const &o){ return new Expr::TypeNames<Expr::String>(o); } ) );
		cl.def("__call__", (const std::string & (Expr::TypeNames<Expr::String>::*)() const) &Expr::TypeNames<Expr::String>::operator(), "C++: Expr::TypeNames<Expr::String>::operator()() const --> const std::string &", pybind11::return_value_policy::automatic);
	}
	{ // Expr::TypeNames file: line:25
		pybind11::class_<Expr::TypeNames<Expr::Bool>, std::shared_ptr<Expr::TypeNames<Expr::Bool>>> cl(M("Expr"), "TypeNames_Expr_Bool_t", "" );
		cl.def( pybind11::init( [](){ return new Expr::TypeNames<Expr::Bool>(); } ) );
		cl.def( pybind11::init( [](Expr::TypeNames<Expr::Bool> const &o){ return new Expr::TypeNames<Expr::Bool>(o); } ) );
		cl.def("__call__", (const std::string & (Expr::TypeNames<Expr::Bool>::*)() const) &Expr::TypeNames<Expr::Bool>::operator(), "C++: Expr::TypeNames<Expr::Bool>::operator()() const --> const std::string &", pybind11::return_value_policy::automatic);
	}
	{ // Expr::TypeNames file: line:25
		pybind11::class_<Expr::TypeNames<Expr::FP, Expr::Bool, Expr::BV, Expr::String>, std::shared_ptr<Expr::TypeNames<Expr::FP, Expr::Bool, Expr::BV, Expr::String>>> cl(M("Expr"), "TypeNames_Expr_FP_Expr_Bool_Expr_BV_Expr_String_t", "" );
		cl.def( pybind11::init( [](){ return new Expr::TypeNames<Expr::FP, Expr::Bool, Expr::BV, Expr::String>(); } ) );
		cl.def( pybind11::init( [](Expr::TypeNames<Expr::FP, Expr::Bool, Expr::BV, Expr::String> const &o){ return new Expr::TypeNames<Expr::FP, Expr::Bool, Expr::BV, Expr::String>(o); } ) );
		cl.def("__call__", (const std::string & (Expr::TypeNames<Expr::FP, Expr::Bool, Expr::BV, Expr::String>::*)() const) &Expr::TypeNames<Expr::FP, Expr::Bool, Expr::BV, Expr::String>::operator(), "C++: Expr::TypeNames<Expr::FP, Expr::Bool, Expr::BV, Expr::String>::operator()() const --> const std::string &", pybind11::return_value_policy::automatic);
	}
	{ // Expr::TypeNames file: line:25
		pybind11::class_<Expr::TypeNames<Expr::FP, Expr::BV>, std::shared_ptr<Expr::TypeNames<Expr::FP, Expr::BV>>> cl(M("Expr"), "TypeNames_Expr_FP_Expr_BV_t", "" );
		cl.def( pybind11::init( [](){ return new Expr::TypeNames<Expr::FP, Expr::BV>(); } ) );
		cl.def( pybind11::init( [](Expr::TypeNames<Expr::FP, Expr::BV> const &o){ return new Expr::TypeNames<Expr::FP, Expr::BV>(o); } ) );
		cl.def("__call__", (const std::string & (Expr::TypeNames<Expr::FP, Expr::BV>::*)() const) &Expr::TypeNames<Expr::FP, Expr::BV>::operator(), "C++: Expr::TypeNames<Expr::FP, Expr::BV>::operator()() const --> const std::string &", pybind11::return_value_policy::automatic);
	}
}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_17.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

// PyObj::Base file: line:21
struct PyCallBack_PyObj_Base : public PyObj::Base {
	using PyObj::Base::Base;

	std::string actual_repr() const override {
		pybind11::gil_scoped_acquire gil;
		pybind11::function overload = pybind11::get_overload(static_cast<const PyObj::Base *>(this), "actual_repr");
		if (overload) {
			auto o = overload.operator()<pybind11::return_value_policy::reference>();
			if (pybind11::detail::cast_is_temporary_value_reference<std::string>::value) {
				static pybind11::detail::override_caster_t<std::string> caster;
				return pybind11::detail::cast_ref<std::string>(std::move(o), caster);
			}
			else return pybind11::detail::cast_safe<std::string>(std::move(o));
		}
		pybind11::pybind11_fail("Tried to call pure virtual function \"Base::actual_repr\"");
	}
};

// PyObj::Sized file: line:40
struct PyCallBack_PyObj_Sized : public PyObj::Sized {
	using PyObj::Sized::Sized;

	std::string actual_repr() const override {
		pybind11::gil_scoped_acquire gil;
		pybind11::function overload = pybind11::get_overload(static_cast<const PyObj::Sized *>(this), "actual_repr");
		if (overload) {
			auto o = overload.operator()<pybind11::return_value_policy::reference>();
			if (pybind11::detail::cast_is_temporary_value_reference<std::string>::value) {
				static pybind11::detail::override_caster_t<std::string> caster;
				return pybind11::detail::cast_ref<std::string>(std::move(o), caster);
			}
			else return pybind11::detail::cast_safe<std::string>(std::move(o));
		}
		pybind11::pybind11_fail("Tried to call pure virtual function \"Base::actual_repr\"");
	}
};

// PyObj::VS file: line:32
struct PyCallBack_PyObj_VS : public PyObj::VS {
	using PyObj::VS::VS;

	std::string actual_repr() const override {
		pybind11::gil_scoped_acquire gil;
		pybind11::function overload = pybind11::get_overload(static_cast<const PyObj::VS *>(this), "actual_repr");
		if (overload) {
			auto o = overload.operator()<pybind11::return_value_policy::reference>();
			if (pybind11::detail::cast_is_temporary_value_reference<std::string>::value) {
				static pybind11::detail::override_caster_t<std::string> caster;
				return pybind11::detail::cast_ref<std::string>(std::move(o), caster);
			}
			else return pybind11::detail::cast_safe<std::string>(std::move(o));
		}
		pybind11::pybind11_fail("Tried to call pure virtual function \"Base::actual_repr\"");
	}
};

namespace API::Binder {
void bind_unknown_unknown_17(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	{ // PyObj::Base file: line:21
		pybind11::class_<PyObj::Base, PyObj::Base*, PyCallBack_PyObj_Base, Hash::Hashed, HasRepr<PyObj::Base>> cl(M("PyObj"), "Base", "A class containing a ref to some python object and a hash\n  Warning: No virtual destructor; do *not* delete by base class pointer; avoid slicing!" );
	}
	{ // PyObj::Sized file: line:40
		pybind11::class_<PyObj::Sized, PyObj::Sized*, PyCallBack_PyObj_Sized, PyObj::Base, BitLength> cl(M("PyObj"), "Sized", "A sized python object\n  Warning: No virtual destructor; do *not* delete by base class pointer; avoid slicing!" );
	}
	{ // PyObj::VS file: line:32
		pybind11::class_<PyObj::VS, PyObj::VS*, PyCallBack_PyObj_VS, PyObj::Sized> cl(M("PyObj"), "VS", "" );
	}
}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_18.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_18(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	// Op::bit_length(const class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt> &) file: line:59
	M("Op").def("bit_length", (unsigned long long (*)(const class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt> &)) &Op::bit_length, "Returns the bit_length of the value stored in v if applicable\n  Note: this is a raw bit_length that does not include implicit null-padding\n  This means for strings, the op bit_length may be shorter than the expr bit length\n  Raise an exception if called on a size without a bit length (like a bool)\n\nC++: Op::bit_length(const class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt> &) --> unsigned long long", pybind11::arg("v"));

	{ // Op::Base file: line:20
		pybind11::class_<Op::Base, std::shared_ptr<Op::Base>, HasRepr<Op::Base>, Factory::FactoryMade> cl(M("Op"), "Base", "Base operation expr\n  All op exprs must subclass this" );
		cl.def("op_name", (const char * (Op::Base::*)() const) &Op::Base::op_name, "The name of the op \n\nC++: Op::Base::op_name() const --> const char *", pybind11::return_value_policy::automatic);
		cl.def("python_children", (class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> > (Op::Base::*)() const) &Op::Base::python_children, "Appends the expr children of the expr to the given vector\n  Note: This should only be used when returning children to python\n\nC++: Op::Base::python_children() const --> class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> >");
		cl.def("is_leaf", (bool (Op::Base::*)() const) &Op::Base::is_leaf, "Return true iff the op is a leaf op \n\nC++: Op::Base::is_leaf() const --> bool");
	}
	{ // Op::Binary file: line:52
		pybind11::class_<Op::Binary<true>, std::shared_ptr<Op::Binary<true>>, Op::Base> cl(M("Op"), "Binary_true_t", "" );
		cl.def_readonly("left", &Op::Binary<true>::left);
		cl.def_readonly("right", &Op::Binary<true>::right);
		cl.def("python_children", (class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> > (Op::Binary<true>::*)() const) &Op::Binary<true>::python_children, "C++: Op::Binary<true>::python_children() const --> class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> >");
		cl.def("op_name", (const char * (Op::Base::*)() const) &Op::Base::op_name, "The name of the op \n\nC++: Op::Base::op_name() const --> const char *", pybind11::return_value_policy::automatic);
		cl.def("python_children", (class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> > (Op::Base::*)() const) &Op::Base::python_children, "Appends the expr children of the expr to the given vector\n  Note: This should only be used when returning children to python\n\nC++: Op::Base::python_children() const --> class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> >");
		cl.def("is_leaf", (bool (Op::Base::*)() const) &Op::Base::is_leaf, "Return true iff the op is a leaf op \n\nC++: Op::Base::is_leaf() const --> bool");
	}
	{ // Op::Binary file: line:52
		pybind11::class_<Op::Binary<false>, std::shared_ptr<Op::Binary<false>>, Op::Base> cl(M("Op"), "Binary_false_t", "" );
		cl.def_readonly("left", &Op::Binary<false>::left);
		cl.def_readonly("right", &Op::Binary<false>::right);
		cl.def("python_children", (class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> > (Op::Binary<false>::*)() const) &Op::Binary<false>::python_children, "C++: Op::Binary<false>::python_children() const --> class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> >");
		cl.def("op_name", (const char * (Op::Base::*)() const) &Op::Base::op_name, "The name of the op \n\nC++: Op::Base::op_name() const --> const char *", pybind11::return_value_policy::automatic);
		cl.def("python_children", (class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> > (Op::Base::*)() const) &Op::Base::python_children, "Appends the expr children of the expr to the given vector\n  Note: This should only be used when returning children to python\n\nC++: Op::Base::python_children() const --> class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> >");
		cl.def("is_leaf", (bool (Op::Base::*)() const) &Op::Base::is_leaf, "Return true iff the op is a leaf op \n\nC++: Op::Base::is_leaf() const --> bool");
	}
	{ // Op::Extract file: line:14
		pybind11::class_<Op::Extract, std::shared_ptr<Op::Extract>, Op::Base> cl(M("Op"), "Extract", "The op class: Extract " );
		cl.def_readonly("high", &Op::Extract::high);
		cl.def_readonly("low", &Op::Extract::low);
		cl.def_readonly("from", &Op::Extract::from);
		cl.def("python_children", (class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> > (Op::Extract::*)() const) &Op::Extract::python_children, "Appends the expr children of the expr to the given vector\n  Note: This should only be used when returning children to python\n\nC++: Op::Extract::python_children() const --> class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> >");
	}
	{ // Op::AbstractFlat file: line:36
		pybind11::class_<Op::AbstractFlat, std::shared_ptr<Op::AbstractFlat>, Op::Base> cl(M("Op"), "AbstractFlat", "An abstract flattened Op class\n  Operands must all be of the same type and there must be at least 2\n  These conditions are *not* validated" );
		cl.def_readonly("operands", &Op::AbstractFlat::operands);
		cl.def("consider_size", (bool (Op::AbstractFlat::*)() const) &Op::AbstractFlat::consider_size, "Return true if this class requires each operand be of the same size \n\nC++: Op::AbstractFlat::consider_size() const --> bool");
		cl.def("python_children", (class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> > (Op::AbstractFlat::*)() const) &Op::AbstractFlat::python_children, "Appends the expr children of the expr to the given vector\n  Note: This should only be used when returning children to python\n\nC++: Op::AbstractFlat::python_children() const --> class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> >");
	}
	{ // Op::Flat file: line:87
		pybind11::class_<Op::Flat<true>, std::shared_ptr<Op::Flat<true>>, Op::AbstractFlat> cl(M("Op"), "Flat_true_t", "" );
		cl.def("consider_size", (bool (Op::Flat<true>::*)() const) &Op::Flat<true>::consider_size, "C++: Op::Flat<true>::consider_size() const --> bool");
		cl.def_readonly("operands", &Op::AbstractFlat::operands);
		cl.def("consider_size", (bool (Op::AbstractFlat::*)() const) &Op::AbstractFlat::consider_size, "Return true if this class requires each operand be of the same size \n\nC++: Op::AbstractFlat::consider_size() const --> bool");
		cl.def("python_children", (class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> > (Op::AbstractFlat::*)() const) &Op::AbstractFlat::python_children, "Appends the expr children of the expr to the given vector\n  Note: This should only be used when returning children to python\n\nC++: Op::AbstractFlat::python_children() const --> class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> >");
	}
	{ // Op::Flat file: line:87
		pybind11::class_<Op::Flat<false>, std::shared_ptr<Op::Flat<false>>, Op::AbstractFlat> cl(M("Op"), "Flat_false_t", "" );
		cl.def("consider_size", (bool (Op::Flat<false>::*)() const) &Op::Flat<false>::consider_size, "C++: Op::Flat<false>::consider_size() const --> bool");
		cl.def_readonly("operands", &Op::AbstractFlat::operands);
		cl.def("consider_size", (bool (Op::AbstractFlat::*)() const) &Op::AbstractFlat::consider_size, "Return true if this class requires each operand be of the same size \n\nC++: Op::AbstractFlat::consider_size() const --> bool");
		cl.def("python_children", (class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> > (Op::AbstractFlat::*)() const) &Op::AbstractFlat::python_children, "Appends the expr children of the expr to the given vector\n  Note: This should only be used when returning children to python\n\nC++: Op::AbstractFlat::python_children() const --> class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> >");
	}
}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_19.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_19(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	{ // Op::FP::From2sComplementBV file: line:15
		pybind11::class_<Op::FP::From2sComplementBV, std::shared_ptr<Op::FP::From2sComplementBV>, Op::Base> cl(M("Op::FP"), "From2sComplementBV", "The op class: Which converts a 2s complement BV into an FP " );
		cl.def_readonly("mode", &Op::FP::From2sComplementBV::mode);
		cl.def_readonly("bv", &Op::FP::From2sComplementBV::bv);
		cl.def_readonly("width", &Op::FP::From2sComplementBV::width);
		cl.def("python_children", (class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> > (Op::FP::From2sComplementBV::*)() const) &Op::FP::From2sComplementBV::python_children, "Appends the expr children of the expr to the given vector\n  Note: This should only be used when returning children to python\n\nC++: Op::FP::From2sComplementBV::python_children() const --> class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> >");
	}
	{ // Op::FP::From2sComplementBVSigned file: line:62
		pybind11::class_<Op::FP::From2sComplementBVSigned, std::shared_ptr<Op::FP::From2sComplementBVSigned>, Op::FP::From2sComplementBV> cl(M("Op::FP"), "From2sComplementBVSigned", "The op class: Which converts a signed 2s complement BV into an FP " );
	}
	{ // Op::FP::From2sComplementBVUnsigned file: line:73
		pybind11::class_<Op::FP::From2sComplementBVUnsigned, std::shared_ptr<Op::FP::From2sComplementBVUnsigned>, Op::FP::From2sComplementBV> cl(M("Op::FP"), "From2sComplementBVUnsigned", "The op class: Which converts a signed 2s complement BV into an FP " );
	}
	{ // Op::FP::FromFP file: line:15
		pybind11::class_<Op::FP::FromFP, std::shared_ptr<Op::FP::FromFP>, Op::Base> cl(M("Op::FP"), "FromFP", "The op class which converts an FP into another FP (for example, a float into a double) " );
		cl.def_readonly("mode", &Op::FP::FromFP::mode);
		cl.def_readonly("fp", &Op::FP::FromFP::fp);
		cl.def_readonly("width", &Op::FP::FromFP::width);
		cl.def("python_children", (class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> > (Op::FP::FromFP::*)() const) &Op::FP::FromFP::python_children, "Appends the expr children of the expr to the given vector\n  Note: This should only be used when returning children to python\n\nC++: Op::FP::FromFP::python_children() const --> class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> >");
	}
	{ // Op::FP::FromNot2sComplementBV file: line:15
		pybind11::class_<Op::FP::FromNot2sComplementBV, std::shared_ptr<Op::FP::FromNot2sComplementBV>, Op::Base> cl(M("Op::FP"), "FromNot2sComplementBV", "The op class which converts a non-2s-complement BV into an FP " );
		cl.def_readonly("bv", &Op::FP::FromNot2sComplementBV::bv);
		cl.def_readonly("width", &Op::FP::FromNot2sComplementBV::width);
		cl.def("python_children", (class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> > (Op::FP::FromNot2sComplementBV::*)() const) &Op::FP::FromNot2sComplementBV::python_children, "Appends the expr children of the expr to the given vector\n  Note: This should only be used when returning children to python\n\nC++: Op::FP::FromNot2sComplementBV::python_children() const --> class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> >");
	}
	{ // Op::FP::ModeBinary file: line:32
		pybind11::class_<Op::FP::ModeBinary, std::shared_ptr<Op::FP::ModeBinary>, Op::Base> cl(M("Op::FP"), "ModeBinary", "An FP Binary Op class\n  Operands must all be of the same type and size" );
		cl.def_readonly("mode", &Op::FP::ModeBinary::mode);
		cl.def_readonly("left", &Op::FP::ModeBinary::left);
		cl.def_readonly("right", &Op::FP::ModeBinary::right);
		cl.def("python_children", (class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> > (Op::FP::ModeBinary::*)() const) &Op::FP::ModeBinary::python_children, "Appends the expr children of the expr to the given vector\n  Note: This should only be used when returning children to python\n\nC++: Op::FP::ModeBinary::python_children() const --> class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> >");
	}
	{ // Op::FP::ToBV file: line:15
		pybind11::class_<Op::FP::ToBV, std::shared_ptr<Op::FP::ToBV>, Op::Base> cl(M("Op::FP"), "ToBV", "The op class: to_bv " );
		cl.def_readonly("mode", &Op::FP::ToBV::mode);
		cl.def_readonly("fp", &Op::FP::ToBV::fp);
		cl.def("python_children", (class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> > (Op::FP::ToBV::*)() const) &Op::FP::ToBV::python_children, "Appends the expr children of the expr to the given vector\n  Note: This should only be used when returning children to python\n\nC++: Op::FP::ToBV::python_children() const --> class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> >");
	}
	{ // Op::FP::ToBVSigned file: line:58
		pybind11::class_<Op::FP::ToBVSigned, std::shared_ptr<Op::FP::ToBVSigned>, Op::FP::ToBV> cl(M("Op::FP"), "ToBVSigned", "Signed ToBV " );
	}
	{ // Op::FP::ToBVUnsigned file: line:72
		pybind11::class_<Op::FP::ToBVUnsigned, std::shared_ptr<Op::FP::ToBVUnsigned>, Op::FP::ToBV> cl(M("Op::FP"), "ToBVUnsigned", "Unsigned ToBV " );
	}
}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_2.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_2(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	{ // CUID::HasCUID file: line:38
		pybind11::class_<CUID::HasCUID, CUID::HasCUID*> cl(M("CUID"), "HasCUID", "A type that has a class unique id\n  This has the benefits of a virtual function as inherited classes\n  can have different CUIDs than their ancestors, while also avoiding\n  the overhead of a vtabel call to invoke virtual cuid() const;\n  Warning: No virtual destructor; do *not* delete by base class pointer; avoid slicing!" );
		cl.def_readonly("cuid", &CUID::HasCUID::cuid);
	}
}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_20.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_20(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	{ // Op::Ternary file: line:33
		pybind11::class_<Op::Ternary<false>, std::shared_ptr<Op::Ternary<false>>, Op::Base> cl(M("Op"), "Ternary_false_t", "" );
		cl.def_readonly("first", &Op::Ternary<false>::first);
		cl.def_readonly("second", &Op::Ternary<false>::second);
		cl.def_readonly("third", &Op::Ternary<false>::third);
		cl.def("python_children", (class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> > (Op::Ternary<false>::*)() const) &Op::Ternary<false>::python_children, "C++: Op::Ternary<false>::python_children() const --> class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> >");
		cl.def("op_name", (const char * (Op::Base::*)() const) &Op::Base::op_name, "The name of the op \n\nC++: Op::Base::op_name() const --> const char *", pybind11::return_value_policy::automatic);
		cl.def("python_children", (class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> > (Op::Base::*)() const) &Op::Base::python_children, "Appends the expr children of the expr to the given vector\n  Note: This should only be used when returning children to python\n\nC++: Op::Base::python_children() const --> class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> >");
		cl.def("is_leaf", (bool (Op::Base::*)() const) &Op::Base::is_leaf, "Return true iff the op is a leaf op \n\nC++: Op::Base::is_leaf() const --> bool");
	}
	{ // Op::Unary file: line:30
		pybind11::class_<Op::Unary, std::shared_ptr<Op::Unary>, Op::Base> cl(M("Op"), "Unary", "A Unary Op class " );
		cl.def_readonly("child", &Op::Unary::child);
		cl.def("python_children", (class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> > (Op::Unary::*)() const) &Op::Unary::python_children, "Appends the expr children of the expr to the given vector\n  Note: This should only be used when returning children to python\n\nC++: Op::Unary::python_children() const --> class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> >");
	}
}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_21.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_21(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	{ // Op::FP::IsNan file: line:22
		pybind11::class_<Op::FP::IsNan, std::shared_ptr<Op::FP::IsNan>, Op::Unary> cl(M("Op::FP"), "IsNan", "The unary fp op class: FP::IsNan " );
	}
	{ // Op::FP::ToIEEEBV file: line:25
		pybind11::class_<Op::FP::ToIEEEBV, std::shared_ptr<Op::FP::ToIEEEBV>, Op::Unary> cl(M("Op::FP"), "ToIEEEBV", "The unary fp op class: FP::ToIEEEBV " );
	}
	{ // Op::FP::Add file: line:34
		pybind11::class_<Op::FP::Add, std::shared_ptr<Op::FP::Add>, Op::FP::ModeBinary> cl(M("Op::FP"), "Add", "The op class: FP::Add\n  Input sizes may not differ" );
	}
	{ // Op::FP::Sub file: line:39
		pybind11::class_<Op::FP::Sub, std::shared_ptr<Op::FP::Sub>, Op::FP::ModeBinary> cl(M("Op::FP"), "Sub", "The op class: FP::Sub\n  Input sizes may not differ" );
	}
	{ // Op::FP::Mul file: line:44
		pybind11::class_<Op::FP::Mul, std::shared_ptr<Op::FP::Mul>, Op::FP::ModeBinary> cl(M("Op::FP"), "Mul", "The op class: FP::Mul\n  Input sizes may not differ" );
	}
	{ // Op::FP::Div file: line:49
		pybind11::class_<Op::FP::Div, std::shared_ptr<Op::FP::Div>, Op::FP::ModeBinary> cl(M("Op::FP"), "Div", "The op class: FP::Div\n  Input sizes may not differ" );
	}
	{ // Op::FP::FP file: line:58
		pybind11::class_<Op::FP::FP, std::shared_ptr<Op::FP::FP>, Op::Ternary<false>> cl(M("Op::FP"), "FP", "The ternary op class: FP::FP\n  Input sizes may differ" );
	}
}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_22.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_22(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	{ // Op::If file: line:14
		pybind11::class_<Op::If, std::shared_ptr<Op::If>, Op::Base> cl(M("Op"), "If", "The op class: If " );
		cl.def_readonly("cond", &Op::If::cond);
		cl.def_readonly("if_true", &Op::If::if_true);
		cl.def_readonly("if_false", &Op::If::if_false);
		cl.def("python_children", (class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> > (Op::If::*)() const) &Op::If::python_children, "Appends the expr children of the expr to the given vector\n  Note: This should only be used when returning children to python\n\nC++: Op::If::python_children() const --> class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> >");
	}
	{ // Op::Literal file: line:18
		pybind11::class_<Op::Literal, std::shared_ptr<Op::Literal>, Op::Base> cl(M("Op"), "Literal", "The op class Literal " );
		cl.def_readonly("value", &Op::Literal::value);
		cl.def("python_children", (class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> > (Op::Literal::*)() const) &Op::Literal::python_children, "Appends the expr children of the expr to the given vector\n  Note: This should only be used when returning children to python\n\nC++: Op::Literal::python_children() const --> class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> >");
		cl.def("is_leaf", (bool (Op::Literal::*)() const) &Op::Literal::is_leaf, "Return true iff the op is a leaf op \n\nC++: Op::Literal::is_leaf() const --> bool");
	}
}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_23.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_23(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	{ // Op::String::IndexOf file: line:14
		pybind11::class_<Op::String::IndexOf, std::shared_ptr<Op::String::IndexOf>, Op::Base> cl(M("Op::String"), "IndexOf", "The op class: String::IndexOf " );
		cl.def_readonly("str", &Op::String::IndexOf::str);
		cl.def_readonly("pattern", &Op::String::IndexOf::pattern);
		cl.def_readonly("start_index", &Op::String::IndexOf::start_index);
		cl.def("python_children", (class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> > (Op::String::IndexOf::*)() const) &Op::String::IndexOf::python_children, "Appends the expr children of the expr to the given vector\n  Note: This should only be used when returning children to python\n\nC++: Op::String::IndexOf::python_children() const --> class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> >");
	}
	{ // Op::String::SubString file: line:14
		pybind11::class_<Op::String::SubString, std::shared_ptr<Op::String::SubString>, Op::Base> cl(M("Op::String"), "SubString", "The op class: String::SubString " );
		cl.def_readonly("start_index", &Op::String::SubString::start_index);
		cl.def_readonly("count", &Op::String::SubString::count);
		cl.def_readonly("full_string", &Op::String::SubString::full_string);
		cl.def("python_children", (class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> > (Op::String::SubString::*)() const) &Op::String::SubString::python_children, "Appends the expr children of the expr to the given vector\n  Note: This should only be used when returning children to python\n\nC++: Op::String::SubString::python_children() const --> class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> >");
	}
}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_24.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_24(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	{ // Op::UIntBinary file: line:32
		pybind11::class_<Op::UIntBinary, std::shared_ptr<Op::UIntBinary>, Op::Base> cl(M("Op"), "UIntBinary", "An Op class that has an Expr operand and an int operand " );
		cl.def_readonly("expr", &Op::UIntBinary::expr);
		cl.def_readonly("integer", &Op::UIntBinary::integer);
		cl.def("python_children", (class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> > (Op::UIntBinary::*)() const) &Op::UIntBinary::python_children, "Appends the expr children of the expr to the given vector\n  Note: This should only be used when returning children to python\n\nC++: Op::UIntBinary::python_children() const --> class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> >");
	}
}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_25.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_25(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	{ // Op::String::IsDigit file: line:21
		pybind11::class_<Op::String::IsDigit, std::shared_ptr<Op::String::IsDigit>, Op::Unary> cl(M("Op::String"), "IsDigit", "The unary string op class: String::IsDigit " );
	}
	{ // Op::String::FromInt file: line:24
		pybind11::class_<Op::String::FromInt, std::shared_ptr<Op::String::FromInt>, Op::Unary> cl(M("Op::String"), "FromInt", "The unary string op class: String::FromInt " );
	}
	{ // Op::String::ToInt file: line:31
		pybind11::class_<Op::String::ToInt, std::shared_ptr<Op::String::ToInt>, Op::UIntBinary> cl(M("Op::String"), "ToInt", "The int binary op class: String::ToInt " );
	}
	{ // Op::String::Len file: line:34
		pybind11::class_<Op::String::Len, std::shared_ptr<Op::String::Len>, Op::UIntBinary> cl(M("Op::String"), "Len", "The int binary op class: String::Len " );
	}
	{ // Op::String::Contains file: line:43
		pybind11::class_<Op::String::Contains, std::shared_ptr<Op::String::Contains>, Op::Binary<false>> cl(M("Op::String"), "Contains", "The string binary op class: String::Contains\n  Input sizes may differ" );
	}
	{ // Op::String::PrefixOf file: line:48
		pybind11::class_<Op::String::PrefixOf, std::shared_ptr<Op::String::PrefixOf>, Op::Binary<false>> cl(M("Op::String"), "PrefixOf", "The string binary op class: String::PrefixOf\n  Input sizes may differ" );
	}
	{ // Op::String::SuffixOf file: line:53
		pybind11::class_<Op::String::SuffixOf, std::shared_ptr<Op::String::SuffixOf>, Op::Binary<false>> cl(M("Op::String"), "SuffixOf", "The string binary op class: String::SuffixOf\n  Input sizes may differ" );
	}
	{ // Op::String::Replace file: line:62
		pybind11::class_<Op::String::Replace, std::shared_ptr<Op::String::Replace>, Op::Ternary<false>> cl(M("Op::String"), "Replace", "The ternary string op class: String::Replace\n  Input sizes may differ" );
	}
}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_26.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_26(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	{ // Op::Symbol file: line:14
		pybind11::class_<Op::Symbol, std::shared_ptr<Op::Symbol>, Op::Base> cl(M("Op"), "Symbol", "The op class Symbol " );
		cl.def_readonly("name", &Op::Symbol::name);
		cl.def("python_children", (class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> > (Op::Symbol::*)() const) &Op::Symbol::python_children, "Appends the expr children of the expr to the given vector\n  Note: This should only be used when returning children to python\n\nC++: Op::Symbol::python_children() const --> class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt, class std::shared_ptr<const class Expr::Base>, enum Mode::FP::Rounding, struct Mode::FP::Width> >");
		cl.def("is_leaf", (bool (Op::Symbol::*)() const) &Op::Symbol::is_leaf, "Return true iff the op is a leaf op \n\nC++: Op::Symbol::is_leaf() const --> bool");
	}
	{ // Op::Abs file: line:25
		pybind11::class_<Op::Abs, std::shared_ptr<Op::Abs>, Op::Unary> cl(M("Op"), "Abs", "The unary mathematical op class: Abs " );
	}
	{ // Op::Neg file: line:28
		pybind11::class_<Op::Neg, std::shared_ptr<Op::Neg>, Op::Unary> cl(M("Op"), "Neg", "The unary op class: Neg " );
	}
	{ // Op::Not file: line:31
		pybind11::class_<Op::Not, std::shared_ptr<Op::Not>, Op::Unary> cl(M("Op"), "Not", "The unary op class: Not " );
	}
	{ // Op::Invert file: line:34
		pybind11::class_<Op::Invert, std::shared_ptr<Op::Invert>, Op::Unary> cl(M("Op"), "Invert", "The unary op class: Invert " );
	}
	{ // Op::Reverse file: line:37
		pybind11::class_<Op::Reverse, std::shared_ptr<Op::Reverse>, Op::Unary> cl(M("Op"), "Reverse", "The unary bitwise op class: Reverse " );
	}
	{ // Op::SignExt file: line:44
		pybind11::class_<Op::SignExt, std::shared_ptr<Op::SignExt>, Op::UIntBinary> cl(M("Op"), "SignExt", "The int binary op class: SignExt " );
	}
	{ // Op::ZeroExt file: line:47
		pybind11::class_<Op::ZeroExt, std::shared_ptr<Op::ZeroExt>, Op::UIntBinary> cl(M("Op"), "ZeroExt", "The int binary op class: ZeroExt " );
	}
	{ // Op::Eq file: line:59
		pybind11::class_<Op::Eq, std::shared_ptr<Op::Eq>, Op::Binary<false>> cl(M("Op"), "Eq", "The binary comparison op class: Eq\n  Requires equal sized inputs\n  TODO: tests" );
	}
	{ // Op::Neq file: line:62
		pybind11::class_<Op::Neq, std::shared_ptr<Op::Neq>, Op::Binary<false>> cl(M("Op"), "Neq", "The binary comparison op class: Neq " );
	}
	{ // Op::Inequality file: line:65
		pybind11::class_<Op::Inequality, std::shared_ptr<Op::Inequality>, Op::Binary<true>> cl(M("Op"), "Inequality", "The binary comparison op class: Inequality " );
	}
	{ // Op::UGE file: line:67
		pybind11::class_<Op::UGE, std::shared_ptr<Op::UGE>, Op::Inequality> cl(M("Op"), "UGE", "Unsigned >= comparison op " );
	}
	{ // Op::UGT file: line:69
		pybind11::class_<Op::UGT, std::shared_ptr<Op::UGT>, Op::Inequality> cl(M("Op"), "UGT", "Unsigned > comparison op " );
	}
	{ // Op::ULE file: line:71
		pybind11::class_<Op::ULE, std::shared_ptr<Op::ULE>, Op::Inequality> cl(M("Op"), "ULE", "Unsigned <= comparison op " );
	}
	{ // Op::ULT file: line:73
		pybind11::class_<Op::ULT, std::shared_ptr<Op::ULT>, Op::Inequality> cl(M("Op"), "ULT", "Unsigned < comparison op " );
	}
	{ // Op::SGE file: line:75
		pybind11::class_<Op::SGE, std::shared_ptr<Op::SGE>, Op::Inequality> cl(M("Op"), "SGE", "Signed >= comparison op " );
	}
	{ // Op::SGT file: line:77
		pybind11::class_<Op::SGT, std::shared_ptr<Op::SGT>, Op::Inequality> cl(M("Op"), "SGT", "Signed > comparison op " );
	}
	{ // Op::SLE file: line:79
		pybind11::class_<Op::SLE, std::shared_ptr<Op::SLE>, Op::Inequality> cl(M("Op"), "SLE", "Signed <= comparison op " );
	}
	{ // Op::SLT file: line:81
		pybind11::class_<Op::SLT, std::shared_ptr<Op::SLT>, Op::Inequality> cl(M("Op"), "SLT", "Signed < comparison op " );
	}
	{ // Op::Sub file: line:88
		pybind11::class_<Op::Sub, std::shared_ptr<Op::Sub>, Op::Binary<true>> cl(M("Op"), "Sub", "The mathematical binary op class: Sub\n  Requires equal sized inputs" );
	}
	{ // Op::Div file: line:93
		pybind11::class_<Op::Div, std::shared_ptr<Op::Div>, Op::Binary<true>> cl(M("Op"), "Div", "The mathematical binary op: Div\n  Requires equal sized inputs" );
	}
	{ // Op::DivSigned file: line:95
		pybind11::class_<Op::DivSigned, std::shared_ptr<Op::DivSigned>, Op::Div> cl(M("Op"), "DivSigned", "The signed div op class " );
	}
	{ // Op::DivUnsigned file: line:97
		pybind11::class_<Op::DivUnsigned, std::shared_ptr<Op::DivUnsigned>, Op::Div> cl(M("Op"), "DivUnsigned", "The unsigned div op class " );
	}
	{ // Op::Mod file: line:102
		pybind11::class_<Op::Mod, std::shared_ptr<Op::Mod>, Op::Binary<true>> cl(M("Op"), "Mod", "The mathematical binary op: Mod\n  Requires equal sized inputs" );
	}
	{ // Op::ModSigned file: line:104
		pybind11::class_<Op::ModSigned, std::shared_ptr<Op::ModSigned>, Op::Div> cl(M("Op"), "ModSigned", "The signed mod op class " );
	}
	{ // Op::ModUnsigned file: line:106
		pybind11::class_<Op::ModUnsigned, std::shared_ptr<Op::ModUnsigned>, Op::Div> cl(M("Op"), "ModUnsigned", "The unsigned mod op class " );
	}
	{ // Op::Shift file: line:113
		pybind11::class_<Op::Shift, std::shared_ptr<Op::Shift>, Op::Binary<true>> cl(M("Op"), "Shift", "The bitwise binary op class: Shift\n  Requires equal sized inputs" );
	}
	{ // Op::ShiftLeft file: line:115
		pybind11::class_<Op::ShiftLeft, std::shared_ptr<Op::ShiftLeft>, Op::Shift> cl(M("Op"), "ShiftLeft", "The bitwise left shift op class " );
	}
	{ // Op::ShiftLogicalRight file: line:117
		pybind11::class_<Op::ShiftLogicalRight, std::shared_ptr<Op::ShiftLogicalRight>, Op::Shift> cl(M("Op"), "ShiftLogicalRight", "The bitwise logical right shift op class " );
	}
	{ // Op::ShiftArithmeticRight file: line:119
		pybind11::class_<Op::ShiftArithmeticRight, std::shared_ptr<Op::ShiftArithmeticRight>, Op::Shift> cl(M("Op"), "ShiftArithmeticRight", "The bitwise arithmetic right shift op class " );
	}
	{ // Op::Rotate file: line:124
		pybind11::class_<Op::Rotate, std::shared_ptr<Op::Rotate>, Op::Binary<true>> cl(M("Op"), "Rotate", "Abstract bitwise binary rotations\n  Requires equal sized inputs" );
	}
	{ // Op::RotateLeft file: line:126
		pybind11::class_<Op::RotateLeft, std::shared_ptr<Op::RotateLeft>, Op::Rotate> cl(M("Op"), "RotateLeft", "The bitwise binary op class: RotateLeft " );
	}
	{ // Op::RotateRight file: line:128
		pybind11::class_<Op::RotateRight, std::shared_ptr<Op::RotateRight>, Op::Rotate> cl(M("Op"), "RotateRight", "The bitwise binary op class: RotateRight " );
	}
	{ // Op::Widen file: line:135
		pybind11::class_<Op::Widen, std::shared_ptr<Op::Widen>, Op::Binary<true>> cl(M("Op"), "Widen", "The set binary op class: Widen\n  Requires equal sized inputs" );
	}
	{ // Op::Union file: line:140
		pybind11::class_<Op::Union, std::shared_ptr<Op::Union>, Op::Binary<true>> cl(M("Op"), "Union", "The set binary op class: Union\n  Requires equal sized inputs" );
	}
	{ // Op::Intersection file: line:145
		pybind11::class_<Op::Intersection, std::shared_ptr<Op::Intersection>, Op::Binary<true>> cl(M("Op"), "Intersection", "The set binary op class: Intersection\n  Requires equal sized inputs" );
	}
	{ // Op::Concat file: line:154
		pybind11::class_<Op::Concat, std::shared_ptr<Op::Concat>, Op::Flat<false>> cl(M("Op"), "Concat", "The flat op class: Concat\n  Input sizes may differ" );
	}
	{ // Op::Add file: line:161
		pybind11::class_<Op::Add, std::shared_ptr<Op::Add>, Op::Flat<true>> cl(M("Op"), "Add", "The flat math op class: Add\n  Requires equal sized inputs" );
	}
	{ // Op::Mul file: line:166
		pybind11::class_<Op::Mul, std::shared_ptr<Op::Mul>, Op::Flat<true>> cl(M("Op"), "Mul", "The flat op class: Mul\n  Requires equal sized inputs" );
	}
	{ // Op::Or file: line:173
		pybind11::class_<Op::Or, std::shared_ptr<Op::Or>, Op::Flat<true>> cl(M("Op"), "Or", "The flat op class: Or\n  Requires equal sized inputs" );
	}
	{ // Op::And file: line:178
		pybind11::class_<Op::And, std::shared_ptr<Op::And>, Op::Flat<true>> cl(M("Op"), "And", "The flat op class: And\n  Requires equal sized inputs" );
	}
	{ // Op::Xor file: line:183
		pybind11::class_<Op::Xor, std::shared_ptr<Op::Xor>, Op::Flat<true>> cl(M("Op"), "Xor", "The flat op class: Xor\n  Requires equal sized inputs" );
	}
}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_27.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_27(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	// Create::extract(const unsigned long long, const unsigned long long, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:16
	M("Create").def("extract", [](const unsigned long long & a0, const unsigned long long & a1, const class std::shared_ptr<const class Expr::Base> & a2) -> std::shared_ptr<const class Expr::Base> { return Create::extract(a0, a1, a2); }, "", pybind11::arg("high"), pybind11::arg("low"), pybind11::arg("from"));
	M("Create").def("extract", (class std::shared_ptr<const class Expr::Base> (*)(const unsigned long long, const unsigned long long, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::extract, "Create an Expr with an Extract op\n  Expr pointers may not be nullptr\n\nC++: Create::extract(const unsigned long long, const unsigned long long, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("high"), pybind11::arg("low"), pybind11::arg("from"), pybind11::arg("d"));

}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_28.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_28(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	// Create::FP::from_2s_complement_bv_signed(const enum Mode::FP::Rounding, const class std::shared_ptr<const class Expr::Base> &, const struct Mode::FP::Width &, class std::optional<class pybind11::dict>) file: line:16
	M("Create::FP").def("from_2s_complement_bv_signed", [](const enum Mode::FP::Rounding & a0, const class std::shared_ptr<const class Expr::Base> & a1, const struct Mode::FP::Width & a2) -> std::shared_ptr<const class Expr::Base> { return Create::FP::from_2s_complement_bv_signed(a0, a1, a2); }, "", pybind11::arg("m"), pybind11::arg("bv"), pybind11::arg("w"));
	M("Create::FP").def("from_2s_complement_bv_signed", (class std::shared_ptr<const class Expr::Base> (*)(const enum Mode::FP::Rounding, const class std::shared_ptr<const class Expr::Base> &, const struct Mode::FP::Width &, class std::optional<class pybind11::dict>)) &Create::FP::from_2s_complement_bv_signed, "Create an Expr with an From2sComplementBVSigned op\n  Expr pointers may not be nullptr\n\nC++: Create::FP::from_2s_complement_bv_signed(const enum Mode::FP::Rounding, const class std::shared_ptr<const class Expr::Base> &, const struct Mode::FP::Width &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("m"), pybind11::arg("bv"), pybind11::arg("w"), pybind11::arg("d"));

	// Create::FP::from_2s_complement_bv_unsigned(const enum Mode::FP::Rounding, const class std::shared_ptr<const class Expr::Base> &, const struct Mode::FP::Width &, class std::optional<class pybind11::dict>) file: line:29
	M("Create::FP").def("from_2s_complement_bv_unsigned", [](const enum Mode::FP::Rounding & a0, const class std::shared_ptr<const class Expr::Base> & a1, const struct Mode::FP::Width & a2) -> std::shared_ptr<const class Expr::Base> { return Create::FP::from_2s_complement_bv_unsigned(a0, a1, a2); }, "", pybind11::arg("m"), pybind11::arg("bv"), pybind11::arg("w"));
	M("Create::FP").def("from_2s_complement_bv_unsigned", (class std::shared_ptr<const class Expr::Base> (*)(const enum Mode::FP::Rounding, const class std::shared_ptr<const class Expr::Base> &, const struct Mode::FP::Width &, class std::optional<class pybind11::dict>)) &Create::FP::from_2s_complement_bv_unsigned, "Create an Expr with an From2sComplementBVUnigned op\n  Expr pointers may not be nullptr\n\nC++: Create::FP::from_2s_complement_bv_unsigned(const enum Mode::FP::Rounding, const class std::shared_ptr<const class Expr::Base> &, const struct Mode::FP::Width &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("m"), pybind11::arg("bv"), pybind11::arg("w"), pybind11::arg("d"));

	// Create::FP::from_fp(const enum Mode::FP::Rounding, const class std::shared_ptr<const class Expr::Base> &, const struct Mode::FP::Width &, class std::optional<class pybind11::dict>) file: line:16
	M("Create::FP").def("from_fp", [](const enum Mode::FP::Rounding & a0, const class std::shared_ptr<const class Expr::Base> & a1, const struct Mode::FP::Width & a2) -> std::shared_ptr<const class Expr::Base> { return Create::FP::from_fp(a0, a1, a2); }, "", pybind11::arg("m"), pybind11::arg("fp"), pybind11::arg("w"));
	M("Create::FP").def("from_fp", (class std::shared_ptr<const class Expr::Base> (*)(const enum Mode::FP::Rounding, const class std::shared_ptr<const class Expr::Base> &, const struct Mode::FP::Width &, class std::optional<class pybind11::dict>)) &Create::FP::from_fp, "Create an Expr with an FromFP op\n  Expr pointers may not be nullptr\n\nC++: Create::FP::from_fp(const enum Mode::FP::Rounding, const class std::shared_ptr<const class Expr::Base> &, const struct Mode::FP::Width &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("m"), pybind11::arg("fp"), pybind11::arg("w"), pybind11::arg("d"));

	// Create::FP::from_not_2s_complement_bv(const class std::shared_ptr<const class Expr::Base> &, const struct Mode::FP::Width &, class std::optional<class pybind11::dict>) file: line:16
	M("Create::FP").def("from_not_2s_complement_bv", [](const class std::shared_ptr<const class Expr::Base> & a0, const struct Mode::FP::Width & a1) -> std::shared_ptr<const class Expr::Base> { return Create::FP::from_not_2s_complement_bv(a0, a1); }, "", pybind11::arg("bv"), pybind11::arg("w"));
	M("Create::FP").def("from_not_2s_complement_bv", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const struct Mode::FP::Width &, class std::optional<class pybind11::dict>)) &Create::FP::from_not_2s_complement_bv, "Create an Expr with an FromNot2sComplementBV op\n  Expr pointers may not be nullptr\n\nC++: Create::FP::from_not_2s_complement_bv(const class std::shared_ptr<const class Expr::Base> &, const struct Mode::FP::Width &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("bv"), pybind11::arg("w"), pybind11::arg("d"));

	// Create::FP::to_bv_signed(const enum Mode::FP::Rounding, const class std::shared_ptr<const class Expr::Base> &, const unsigned long long, class std::optional<class pybind11::dict>) file: line:16
	M("Create::FP").def("to_bv_signed", [](const enum Mode::FP::Rounding & a0, const class std::shared_ptr<const class Expr::Base> & a1, const unsigned long long & a2) -> std::shared_ptr<const class Expr::Base> { return Create::FP::to_bv_signed(a0, a1, a2); }, "", pybind11::arg("mode"), pybind11::arg("fp"), pybind11::arg("bit_length"));
	M("Create::FP").def("to_bv_signed", (class std::shared_ptr<const class Expr::Base> (*)(const enum Mode::FP::Rounding, const class std::shared_ptr<const class Expr::Base> &, const unsigned long long, class std::optional<class pybind11::dict>)) &Create::FP::to_bv_signed, "Create an Expr with a ToBVSigned op\n  Expr pointers may not be nullptr\n\nC++: Create::FP::to_bv_signed(const enum Mode::FP::Rounding, const class std::shared_ptr<const class Expr::Base> &, const unsigned long long, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("mode"), pybind11::arg("fp"), pybind11::arg("bit_length"), pybind11::arg("d"));

	// Create::FP::to_bv_unsigned(const enum Mode::FP::Rounding, const class std::shared_ptr<const class Expr::Base> &, const unsigned long long, class std::optional<class pybind11::dict>) file: line:26
	M("Create::FP").def("to_bv_unsigned", [](const enum Mode::FP::Rounding & a0, const class std::shared_ptr<const class Expr::Base> & a1, const unsigned long long & a2) -> std::shared_ptr<const class Expr::Base> { return Create::FP::to_bv_unsigned(a0, a1, a2); }, "", pybind11::arg("mode"), pybind11::arg("fp"), pybind11::arg("bit_length"));
	M("Create::FP").def("to_bv_unsigned", (class std::shared_ptr<const class Expr::Base> (*)(const enum Mode::FP::Rounding, const class std::shared_ptr<const class Expr::Base> &, const unsigned long long, class std::optional<class pybind11::dict>)) &Create::FP::to_bv_unsigned, "Create an Expr with a ToBVUnsigned op\n  Expr pointers may not be nullptr\n\nC++: Create::FP::to_bv_unsigned(const enum Mode::FP::Rounding, const class std::shared_ptr<const class Expr::Base> &, const unsigned long long, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("mode"), pybind11::arg("fp"), pybind11::arg("bit_length"), pybind11::arg("d"));

}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_29.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_29(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	// Create::FP::is_nan(const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:24
	M("Create::FP").def("is_nan", [](const class std::shared_ptr<const class Expr::Base> & a0) -> std::shared_ptr<const class Expr::Base> { return Create::FP::is_nan(a0); }, "", pybind11::arg("x"));
	M("Create::FP").def("is_nan", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::FP::is_nan, "Create a Expr with an FP::IsNan op\n  Expr pointers may not be nullptr\n\nC++: Create::FP::is_nan(const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("x"), pybind11::arg("d"));

	// Create::FP::to_ieee_bv(const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:31
	M("Create::FP").def("to_ieee_bv", [](const class std::shared_ptr<const class Expr::Base> & a0) -> std::shared_ptr<const class Expr::Base> { return Create::FP::to_ieee_bv(a0); }, "", pybind11::arg("x"));
	M("Create::FP").def("to_ieee_bv", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::FP::to_ieee_bv, "Create a Expr with an FP::ToIEEEBV op\n  Expr pointers may not be nullptr\n\nC++: Create::FP::to_ieee_bv(const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("x"), pybind11::arg("d"));

	// Create::FP::add(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, const enum Mode::FP::Rounding, class std::optional<class pybind11::dict>) file: line:48
	M("Create::FP").def("add", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1, const enum Mode::FP::Rounding & a2) -> std::shared_ptr<const class Expr::Base> { return Create::FP::add(a0, a1, a2); }, "", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("mode"));
	M("Create::FP").def("add", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, const enum Mode::FP::Rounding, class std::optional<class pybind11::dict>)) &Create::FP::add, "C++: Create::FP::add(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, const enum Mode::FP::Rounding, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("mode"), pybind11::arg("d"));

	// Create::FP::sub(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, const enum Mode::FP::Rounding, class std::optional<class pybind11::dict>) file: line:52
	M("Create::FP").def("sub", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1, const enum Mode::FP::Rounding & a2) -> std::shared_ptr<const class Expr::Base> { return Create::FP::sub(a0, a1, a2); }, "", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("mode"));
	M("Create::FP").def("sub", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, const enum Mode::FP::Rounding, class std::optional<class pybind11::dict>)) &Create::FP::sub, "C++: Create::FP::sub(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, const enum Mode::FP::Rounding, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("mode"), pybind11::arg("d"));

	// Create::FP::mul(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, const enum Mode::FP::Rounding, class std::optional<class pybind11::dict>) file: line:56
	M("Create::FP").def("mul", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1, const enum Mode::FP::Rounding & a2) -> std::shared_ptr<const class Expr::Base> { return Create::FP::mul(a0, a1, a2); }, "", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("mode"));
	M("Create::FP").def("mul", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, const enum Mode::FP::Rounding, class std::optional<class pybind11::dict>)) &Create::FP::mul, "C++: Create::FP::mul(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, const enum Mode::FP::Rounding, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("mode"), pybind11::arg("d"));

	// Create::FP::div(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, const enum Mode::FP::Rounding, class std::optional<class pybind11::dict>) file: line:60
	M("Create::FP").def("div", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1, const enum Mode::FP::Rounding & a2) -> std::shared_ptr<const class Expr::Base> { return Create::FP::div(a0, a1, a2); }, "", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("mode"));
	M("Create::FP").def("div", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, const enum Mode::FP::Rounding, class std::optional<class pybind11::dict>)) &Create::FP::div, "C++: Create::FP::div(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, const enum Mode::FP::Rounding, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("mode"), pybind11::arg("d"));

	// Create::FP::fp(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:71
	M("Create::FP").def("fp", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1, const class std::shared_ptr<const class Expr::Base> & a2) -> std::shared_ptr<const class Expr::Base> { return Create::FP::fp(a0, a1, a2); }, "", pybind11::arg("first"), pybind11::arg("second"), pybind11::arg("third"));
	M("Create::FP").def("fp", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::FP::fp, "Create an Expr with an FP::FP op\n  Expr pointers may not be nullptr\n\nC++: Create::FP::fp(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("first"), pybind11::arg("second"), pybind11::arg("third"), pybind11::arg("d"));

}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_3.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_3(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	{ // Hash::Hashed file: line:19
		pybind11::class_<Hash::Hashed, Hash::Hashed*> cl(M("Hash"), "Hashed", "A type that has a precomputed hash value\n  Warning: No virtual destructor; do *not* delete by base class pointer; avoid slicing!" );
		cl.def_readonly("hash", &Hash::Hashed::hash);
		cl.def("__hash__", (long long (Hash::Hashed::*)()) &Hash::Hashed::__hash__, "Get the python hash (a signed 64-bit int) \n\nC++: Hash::Hashed::__hash__() --> long long");
	}
}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_30.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_30(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	// Create::if_(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:16
	M("Create").def("if_", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1, const class std::shared_ptr<const class Expr::Base> & a2) -> std::shared_ptr<const class Expr::Base> { return Create::if_(a0, a1, a2); }, "", pybind11::arg("cond"), pybind11::arg("left"), pybind11::arg("right"));
	M("Create").def("if_", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::if_, "Create an Expr with an If op\n  Expr pointers may not be nullptr\n\nC++: Create::if_(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("cond"), pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("d"));

	// Create::literal_bool(bool, class std::optional<class pybind11::dict>) file: line:110
	M("Create").def("literal_bool", [](bool const & a0) -> std::shared_ptr<const class Expr::Base> { return Create::literal_bool(a0); }, "", pybind11::arg("data"));
	M("Create").def("literal_bool", (class std::shared_ptr<const class Expr::Base> (*)(bool, class std::optional<class pybind11::dict>)) &Create::literal_bool, "C++: Create::literal_bool(bool, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("data"), pybind11::arg("d"));

	// Create::literal_vs(class std::shared_ptr<const class PyObj::VS>, class std::optional<class pybind11::dict>) file: line:111
	M("Create").def("literal_vs", [](class std::shared_ptr<const class PyObj::VS> const & a0) -> std::shared_ptr<const class Expr::Base> { return Create::literal_vs(a0); }, "", pybind11::arg("data"));
	M("Create").def("literal_vs", (class std::shared_ptr<const class Expr::Base> (*)(class std::shared_ptr<const class PyObj::VS>, class std::optional<class pybind11::dict>)) &Create::literal_vs, "C++: Create::literal_vs(class std::shared_ptr<const class PyObj::VS>, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("data"), pybind11::arg("d"));

	// Create::literal_string(std::string, class std::optional<class pybind11::dict>) file: line:112
	M("Create").def("literal_string", [](std::string const & a0) -> std::shared_ptr<const class Expr::Base> { return Create::literal_string(a0); }, "", pybind11::arg("data"));
	M("Create").def("literal_string", (class std::shared_ptr<const class Expr::Base> (*)(std::string, class std::optional<class pybind11::dict>)) &Create::literal_string, "C++: Create::literal_string(std::string, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("data"), pybind11::arg("d"));

	// Create::literal_string(std::string, const unsigned long long, class std::optional<class pybind11::dict>) file: line:50
	M("Create").def("literal_string", [](std::string const & a0, const unsigned long long & a1) -> std::shared_ptr<const class Expr::Base> { return Create::literal_string(a0, a1); }, "", pybind11::arg("data"), pybind11::arg("byte_length"));
	M("Create").def("literal_string", (class std::shared_ptr<const class Expr::Base> (*)(std::string, const unsigned long long, class std::optional<class pybind11::dict>)) &Create::literal_string, "Create a String Expr with a Literal op with a specific size\n  Note: data is implicitly padded with 0s on the right to meet length\n  Note: length is taken in as a byte length, not a bit length\n\nC++: Create::literal_string(std::string, const unsigned long long, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("data"), pybind11::arg("byte_length"), pybind11::arg("d"));

	// Create::literal_fp(const double, const unsigned long long, class std::optional<class pybind11::dict>) file: line:65
	M("Create").def("literal_fp", [](const double & a0, const unsigned long long & a1) -> std::shared_ptr<const class Expr::Base> { return Create::literal_fp(a0, a1); }, "", pybind11::arg("data"), pybind11::arg("bit_length"));
	M("Create").def("literal_fp", (class std::shared_ptr<const class Expr::Base> (*)(const double, const unsigned long long, class std::optional<class pybind11::dict>)) &Create::literal_fp, "Create a FP Expr with a Literal op containing of bit length bit_length\n  Warning: this may cast data to a smaller size (bit_length or greater)\n  Note: bit_length instead of overrides or template b/c python bindings\n  Specifically, only one override would ever be used\n  TODO: later allow Width instead of bit_length (they should be the same size)\n\nC++: Create::literal_fp(const double, const unsigned long long, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("data"), pybind11::arg("bit_length"), pybind11::arg("d"));

	// Create::literal_bv(const unsigned long long, const unsigned long long, class std::optional<class pybind11::dict>) file: line:87
	M("Create").def("literal_bv", [](const unsigned long long & a0, const unsigned long long & a1) -> std::shared_ptr<const class Expr::Base> { return Create::literal_bv(a0, a1); }, "", pybind11::arg("data"), pybind11::arg("bit_length"));
	M("Create").def("literal_bv", (class std::shared_ptr<const class Expr::Base> (*)(const unsigned long long, const unsigned long long, class std::optional<class pybind11::dict>)) &Create::literal_bv, "Create a BV Expr with a Literal op of a given bit length from a U64\n  Warning: this may cast data to a smaller size (bit_length or greater)\n  Note: bit_length instead of overrides or template b/c python bindings\n  Specifically: pybind11 tries methods in order, so we'd have to be very\n  careful to ensure U8 methods were defined before U16, etc; then using\n  U64 would fail 4 overrides and be slow.\n\nC++: Create::literal_bv(const unsigned long long, const unsigned long long, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("data"), pybind11::arg("bit_length"), pybind11::arg("d"));

	// Create::literal_bv(struct BigInt, class std::optional<class pybind11::dict>) file: line:104
	M("Create").def("literal_bv", [](struct BigInt const & a0) -> std::shared_ptr<const class Expr::Base> { return Create::literal_bv(a0); }, "", pybind11::arg("data"));
	M("Create").def("literal_bv", (class std::shared_ptr<const class Expr::Base> (*)(struct BigInt, class std::optional<class pybind11::dict>)) &Create::literal_bv, "Create a BV Expr with a Literal op from a BigInt \n\nC++: Create::literal_bv(struct BigInt, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("data"), pybind11::arg("d"));

	// Create::literal_bv(std::string, const unsigned long long, class std::optional<class pybind11::dict>) file: line:112
	M("Create").def("literal_bv", [](std::string const & a0, const unsigned long long & a1) -> std::shared_ptr<const class Expr::Base> { return Create::literal_bv(a0, a1); }, "", pybind11::arg("data"), pybind11::arg("bit_length"));
	M("Create").def("literal_bv", (class std::shared_ptr<const class Expr::Base> (*)(std::string, const unsigned long long, class std::optional<class pybind11::dict>)) &Create::literal_bv, "Create a BV Expr with a Literal op containing an arbitrary length int\n  Warning: this may cast data to a smaller size (bit_length or greater)\n  data should be a base 10 string containing\n\nC++: Create::literal_bv(std::string, const unsigned long long, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("data"), pybind11::arg("bit_length"), pybind11::arg("d"));

}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_31.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_31(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	// Create::String::from_int(const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:20
	M("Create::String").def("from_int", [](const class std::shared_ptr<const class Expr::Base> & a0) -> std::shared_ptr<const class Expr::Base> { return Create::String::from_int(a0); }, "", pybind11::arg("x"));
	M("Create::String").def("from_int", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::String::from_int, "Create an Expr with a String::FromInt op\n  Note: Currently Ints are taken in as BVs\n  Note: For now, we just set the size to 2 bytes larger than the input\n  This should be large-enough, and isn't as bad an over-estimation as INT_MAX or anything\n  Expr pointers may not be nullptr\n  Note: This is not trivial due to its length calculation\n\nC++: Create::String::from_int(const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("x"), pybind11::arg("d"));

	// Create::String::index_of(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, const unsigned long long, class std::optional<class pybind11::dict>) file: line:16
	M("Create::String").def("index_of", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1, const class std::shared_ptr<const class Expr::Base> & a2, const unsigned long long & a3) -> std::shared_ptr<const class Expr::Base> { return Create::String::index_of(a0, a1, a2, a3); }, "", pybind11::arg("str"), pybind11::arg("pattern"), pybind11::arg("start_index"), pybind11::arg("bit_length"));
	M("Create::String").def("index_of", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, const unsigned long long, class std::optional<class pybind11::dict>)) &Create::String::index_of, "Create an Expr with a String::IndexOf op\n  Expr pointers may not be nullptr\n\nC++: Create::String::index_of(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, const unsigned long long, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("str"), pybind11::arg("pattern"), pybind11::arg("start_index"), pybind11::arg("bit_length"), pybind11::arg("d"));

	// Create::String::replace(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:17
	M("Create::String").def("replace", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1, const class std::shared_ptr<const class Expr::Base> & a2) -> std::shared_ptr<const class Expr::Base> { return Create::String::replace(a0, a1, a2); }, "", pybind11::arg("full"), pybind11::arg("search"), pybind11::arg("replacement"));
	M("Create::String").def("replace", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::String::replace, "Create an Expr with a String::Replace op\n  Despite being ternary, this is not a trivial op because of the unique length calculation\n  Expr pointers may not be nullptr\n\nC++: Create::String::replace(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("full"), pybind11::arg("search"), pybind11::arg("replacement"), pybind11::arg("d"));

}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_32.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_32(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	// Create::String::sub_string(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:43
	M("Create::String").def("sub_string", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1, const class std::shared_ptr<const class Expr::Base> & a2) -> std::shared_ptr<const class Expr::Base> { return Create::String::sub_string(a0, a1, a2); }, "", pybind11::arg("start_index"), pybind11::arg("count"), pybind11::arg("full_string"));
	M("Create::String").def("sub_string", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::String::sub_string, "Create an Expr with a String::SubString op\n  Expr pointers may not be nullptr\n\nC++: Create::String::sub_string(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("start_index"), pybind11::arg("count"), pybind11::arg("full_string"), pybind11::arg("d"));

}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_33.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_33(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	// Create::String::is_digit(const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:22
	M("Create::String").def("is_digit", [](const class std::shared_ptr<const class Expr::Base> & a0) -> std::shared_ptr<const class Expr::Base> { return Create::String::is_digit(a0); }, "", pybind11::arg("x"));
	M("Create::String").def("is_digit", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::String::is_digit, "Create a bool Expr with an String::IsDigit op\n  Expr pointers may not be nullptr\n\nC++: Create::String::is_digit(const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("x"), pybind11::arg("d"));

	// Create::String::to_int(const class std::shared_ptr<const class Expr::Base> &, const unsigned long long, class std::optional<class pybind11::dict>) file: line:35
	M("Create::String").def("to_int", [](const class std::shared_ptr<const class Expr::Base> & a0, const unsigned long long & a1) -> std::shared_ptr<const class Expr::Base> { return Create::String::to_int(a0, a1); }, "", pybind11::arg("expr"), pybind11::arg("output_bit_length"));
	M("Create::String").def("to_int", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const unsigned long long, class std::optional<class pybind11::dict>)) &Create::String::to_int, "Create an Expr with an String::SignExt op\n  Note: Currently Ints are taken in as BVs\n  Expr pointers may not be nullptr\n\nC++: Create::String::to_int(const class std::shared_ptr<const class Expr::Base> &, const unsigned long long, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("expr"), pybind11::arg("output_bit_length"), pybind11::arg("d"));

	// Create::String::len(const class std::shared_ptr<const class Expr::Base> &, const unsigned long long, class std::optional<class pybind11::dict>) file: line:46
	M("Create::String").def("len", [](const class std::shared_ptr<const class Expr::Base> & a0, const unsigned long long & a1) -> std::shared_ptr<const class Expr::Base> { return Create::String::len(a0, a1); }, "", pybind11::arg("expr"), pybind11::arg("output_bit_length"));
	M("Create::String").def("len", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const unsigned long long, class std::optional<class pybind11::dict>)) &Create::String::len, "Create an Expr with an String::Len op\n  Note: Currently Ints are output as BVs\n  Expr pointers may not be nullptr\n\nC++: Create::String::len(const class std::shared_ptr<const class Expr::Base> &, const unsigned long long, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("expr"), pybind11::arg("output_bit_length"), pybind11::arg("d"));

	// Create::String::contains(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:60
	M("Create::String").def("contains", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1) -> std::shared_ptr<const class Expr::Base> { return Create::String::contains(a0, a1); }, "", pybind11::arg("left"), pybind11::arg("right"));
	M("Create::String").def("contains", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::String::contains, "Create an Expr with a String::Contains op\n  Expr pointers may not be nullptr\n\nC++: Create::String::contains(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("d"));

	// Create::String::prefix_of(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:70
	M("Create::String").def("prefix_of", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1) -> std::shared_ptr<const class Expr::Base> { return Create::String::prefix_of(a0, a1); }, "", pybind11::arg("left"), pybind11::arg("right"));
	M("Create::String").def("prefix_of", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::String::prefix_of, "Create an Expr with a String::PrefixOf op\n  Expr pointers may not be nullptr\n\nC++: Create::String::prefix_of(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("d"));

	// Create::String::suffix_of(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:80
	M("Create::String").def("suffix_of", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1) -> std::shared_ptr<const class Expr::Base> { return Create::String::suffix_of(a0, a1); }, "", pybind11::arg("left"), pybind11::arg("right"));
	M("Create::String").def("suffix_of", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::String::suffix_of, "Create an Expr with a String::SuffixOf op\n  Expr pointers may not be nullptr\n\nC++: Create::String::suffix_of(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("d"));

}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_34.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_34(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	// Create::symbol_bool(std::string, class std::optional<class pybind11::dict>) file: line:32
	M("Create").def("symbol_bool", [](std::string const & a0) -> std::shared_ptr<const class Expr::Base> { return Create::symbol_bool(a0); }, "", pybind11::arg("name"));
	M("Create").def("symbol_bool", (class std::shared_ptr<const class Expr::Base> (*)(std::string, class std::optional<class pybind11::dict>)) &Create::symbol_bool, "Create a Bool Expr with a symbol op \n\nC++: Create::symbol_bool(std::string, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("name"), pybind11::arg("d"));

	// Create::symbol_string(std::string, const unsigned long long, class std::optional<class pybind11::dict>) file: line:40
	M("Create").def("symbol_string", [](std::string const & a0, const unsigned long long & a1) -> std::shared_ptr<const class Expr::Base> { return Create::symbol_string(a0, a1); }, "", pybind11::arg("name"), pybind11::arg("byte_length"));
	M("Create").def("symbol_string", (class std::shared_ptr<const class Expr::Base> (*)(std::string, const unsigned long long, class std::optional<class pybind11::dict>)) &Create::symbol_string, "Create a String Expr with a symbol op\n  Note: length is taken in as a byte length, not a bit length\n\nC++: Create::symbol_string(std::string, const unsigned long long, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("name"), pybind11::arg("byte_length"), pybind11::arg("d"));

	// Create::symbol_bv(std::string, const unsigned long long, class std::optional<class pybind11::dict>) file: line:158
	M("Create").def("symbol_bv", [](std::string const & a0, const unsigned long long & a1) -> std::shared_ptr<const class Expr::Base> { return Create::symbol_bv(a0, a1); }, "", pybind11::arg("name"), pybind11::arg("bit_length"));
	M("Create").def("symbol_bv", (class std::shared_ptr<const class Expr::Base> (*)(std::string, const unsigned long long, class std::optional<class pybind11::dict>)) &Create::symbol_bv, "C++: Create::symbol_bv(std::string, const unsigned long long, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("name"), pybind11::arg("bit_length"), pybind11::arg("d"));

	// Create::symbol_fp(std::string, const unsigned long long, class std::optional<class pybind11::dict>) file: line:159
	M("Create").def("symbol_fp", [](std::string const & a0, const unsigned long long & a1) -> std::shared_ptr<const class Expr::Base> { return Create::symbol_fp(a0, a1); }, "", pybind11::arg("name"), pybind11::arg("bit_length"));
	M("Create").def("symbol_fp", (class std::shared_ptr<const class Expr::Base> (*)(std::string, const unsigned long long, class std::optional<class pybind11::dict>)) &Create::symbol_fp, "C++: Create::symbol_fp(std::string, const unsigned long long, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("name"), pybind11::arg("bit_length"), pybind11::arg("d"));

	// Create::symbol_vs(std::string, const unsigned long long, class std::optional<class pybind11::dict>) file: line:160
	M("Create").def("symbol_vs", [](std::string const & a0, const unsigned long long & a1) -> std::shared_ptr<const class Expr::Base> { return Create::symbol_vs(a0, a1); }, "", pybind11::arg("name"), pybind11::arg("bit_length"));
	M("Create").def("symbol_vs", (class std::shared_ptr<const class Expr::Base> (*)(std::string, const unsigned long long, class std::optional<class pybind11::dict>)) &Create::symbol_vs, "C++: Create::symbol_vs(std::string, const unsigned long long, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("name"), pybind11::arg("bit_length"), pybind11::arg("d"));

}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_35.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_35(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	// Create::abs(const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:24
	M("Create").def("abs", [](const class std::shared_ptr<const class Expr::Base> & a0) -> std::shared_ptr<const class Expr::Base> { return Create::abs(a0); }, "", pybind11::arg("x"));
	M("Create").def("abs", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::abs, "Create an Expr with an Abs op\n  Expr pointers may not be nullptr\n\nC++: Create::abs(const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("x"), pybind11::arg("d"));

	// Create::neg(const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:31
	M("Create").def("neg", [](const class std::shared_ptr<const class Expr::Base> & a0) -> std::shared_ptr<const class Expr::Base> { return Create::neg(a0); }, "", pybind11::arg("x"));
	M("Create").def("neg", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::neg, "Create an Expr with an Neg op\n  Expr pointers may not be nullptr\n\nC++: Create::neg(const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("x"), pybind11::arg("d"));

	// Create::not_(const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:38
	M("Create").def("not_", [](const class std::shared_ptr<const class Expr::Base> & a0) -> std::shared_ptr<const class Expr::Base> { return Create::not_(a0); }, "", pybind11::arg("x"));
	M("Create").def("not_", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::not_, "Create an Expr with an Not op\n  Expr pointers may not be nullptr\n\nC++: Create::not_(const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("x"), pybind11::arg("d"));

	// Create::invert(const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:45
	M("Create").def("invert", [](const class std::shared_ptr<const class Expr::Base> & a0) -> std::shared_ptr<const class Expr::Base> { return Create::invert(a0); }, "", pybind11::arg("x"));
	M("Create").def("invert", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::invert, "Create an Expr with an Invert op\n  Expr pointers may not be nullptr\n\nC++: Create::invert(const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("x"), pybind11::arg("d"));

	// Create::reverse(const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:52
	M("Create").def("reverse", [](const class std::shared_ptr<const class Expr::Base> & a0) -> std::shared_ptr<const class Expr::Base> { return Create::reverse(a0); }, "", pybind11::arg("x"));
	M("Create").def("reverse", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::reverse, "Create an Expr with an Reverse op\n  Expr pointers may not be nullptr\n\nC++: Create::reverse(const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("x"), pybind11::arg("d"));

	// Create::sign_ext(const class std::shared_ptr<const class Expr::Base> &, const unsigned long long, class std::optional<class pybind11::dict>) file: line:63
	M("Create").def("sign_ext", [](const class std::shared_ptr<const class Expr::Base> & a0, const unsigned long long & a1) -> std::shared_ptr<const class Expr::Base> { return Create::sign_ext(a0, a1); }, "", pybind11::arg("expr"), pybind11::arg("integer"));
	M("Create").def("sign_ext", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const unsigned long long, class std::optional<class pybind11::dict>)) &Create::sign_ext, "Create an Expr with an SignExt op\n  Expr pointers may not be nullptr\n\nC++: Create::sign_ext(const class std::shared_ptr<const class Expr::Base> &, const unsigned long long, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("expr"), pybind11::arg("integer"), pybind11::arg("d"));

	// Create::zero_ext(const class std::shared_ptr<const class Expr::Base> &, const unsigned long long, class std::optional<class pybind11::dict>) file: line:72
	M("Create").def("zero_ext", [](const class std::shared_ptr<const class Expr::Base> & a0, const unsigned long long & a1) -> std::shared_ptr<const class Expr::Base> { return Create::zero_ext(a0, a1); }, "", pybind11::arg("expr"), pybind11::arg("integer"));
	M("Create").def("zero_ext", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const unsigned long long, class std::optional<class pybind11::dict>)) &Create::zero_ext, "Create an Expr with an ZeroExt op\n  Expr pointers may not be nullptr\n\nC++: Create::zero_ext(const class std::shared_ptr<const class Expr::Base> &, const unsigned long long, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("expr"), pybind11::arg("integer"), pybind11::arg("d"));

	// Create::eq(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:87
	M("Create").def("eq", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1) -> std::shared_ptr<const class Expr::Base> { return Create::eq(a0, a1); }, "", pybind11::arg("left"), pybind11::arg("right"));
	M("Create").def("eq", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::eq, "Create a Bool Expr with an Eq op\n  Expr pointers may not be nullptr\n\nC++: Create::eq(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("d"));

	// Create::neq(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:97
	M("Create").def("neq", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1) -> std::shared_ptr<const class Expr::Base> { return Create::neq(a0, a1); }, "", pybind11::arg("left"), pybind11::arg("right"));
	M("Create").def("neq", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::neq, "Create a Bool Expr with an Neq op\n  Expr pointers may not be nullptr\n\nC++: Create::neq(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("d"));

	// Create::uge(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:120
	M("Create").def("uge", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1) -> std::shared_ptr<const class Expr::Base> { return Create::uge(a0, a1); }, "", pybind11::arg("left"), pybind11::arg("right"));
	M("Create").def("uge", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::uge, "A shortcut for inequality<UGE>; exists for the API \n\nC++: Create::uge(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("d"));

	// Create::ugt(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:126
	M("Create").def("ugt", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1) -> std::shared_ptr<const class Expr::Base> { return Create::ugt(a0, a1); }, "", pybind11::arg("left"), pybind11::arg("right"));
	M("Create").def("ugt", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::ugt, "A shortcut for inequality<UGT>; exists for the API \n\nC++: Create::ugt(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("d"));

	// Create::ule(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:132
	M("Create").def("ule", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1) -> std::shared_ptr<const class Expr::Base> { return Create::ule(a0, a1); }, "", pybind11::arg("left"), pybind11::arg("right"));
	M("Create").def("ule", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::ule, "A shortcut for inequality<ULE>; exists for the API \n\nC++: Create::ule(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("d"));

	// Create::ult(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:138
	M("Create").def("ult", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1) -> std::shared_ptr<const class Expr::Base> { return Create::ult(a0, a1); }, "", pybind11::arg("left"), pybind11::arg("right"));
	M("Create").def("ult", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::ult, "A shortcut for inequality<ULT>; exists for the API \n\nC++: Create::ult(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("d"));

	// Create::sge(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:144
	M("Create").def("sge", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1) -> std::shared_ptr<const class Expr::Base> { return Create::sge(a0, a1); }, "", pybind11::arg("left"), pybind11::arg("right"));
	M("Create").def("sge", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::sge, "A shortcut for inequality<SGE>; exists for the API \n\nC++: Create::sge(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("d"));

	// Create::sgt(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:150
	M("Create").def("sgt", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1) -> std::shared_ptr<const class Expr::Base> { return Create::sgt(a0, a1); }, "", pybind11::arg("left"), pybind11::arg("right"));
	M("Create").def("sgt", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::sgt, "A shortcut for inequality<SGT>; exists for the API \n\nC++: Create::sgt(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("d"));

	// Create::sle(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:156
	M("Create").def("sle", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1) -> std::shared_ptr<const class Expr::Base> { return Create::sle(a0, a1); }, "", pybind11::arg("left"), pybind11::arg("right"));
	M("Create").def("sle", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::sle, "A shortcut for inequality<SLE>; exists for the API \n\nC++: Create::sle(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("d"));

	// Create::slt(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:162
	M("Create").def("slt", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1) -> std::shared_ptr<const class Expr::Base> { return Create::slt(a0, a1); }, "", pybind11::arg("left"), pybind11::arg("right"));
	M("Create").def("slt", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::slt, "A shortcut for inequality<SLT>; exists for the API \n\nC++: Create::slt(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("d"));

	// Create::sub(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:172
	M("Create").def("sub", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1) -> std::shared_ptr<const class Expr::Base> { return Create::sub(a0, a1); }, "", pybind11::arg("left"), pybind11::arg("right"));
	M("Create").def("sub", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::sub, "Create an Expr with an Sub op\n  Expr pointers may not be nullptr\n\nC++: Create::sub(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("d"));

}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_36.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_36(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	// Create::div_signed(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:181
	M("Create").def("div_signed", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1) -> std::shared_ptr<const class Expr::Base> { return Create::div_signed(a0, a1); }, "", pybind11::arg("left"), pybind11::arg("right"));
	M("Create").def("div_signed", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::div_signed, "Create an Expr with a DivSigned op\n  Expr pointers may not be nullptr\n\nC++: Create::div_signed(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("d"));

	// Create::div_unsigned(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:190
	M("Create").def("div_unsigned", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1) -> std::shared_ptr<const class Expr::Base> { return Create::div_unsigned(a0, a1); }, "", pybind11::arg("left"), pybind11::arg("right"));
	M("Create").def("div_unsigned", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::div_unsigned, "Create an Expr with a DivUnsigned op\n  Expr pointers may not be nullptr\n\nC++: Create::div_unsigned(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("d"));

	// Create::mod_signed(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:199
	M("Create").def("mod_signed", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1) -> std::shared_ptr<const class Expr::Base> { return Create::mod_signed(a0, a1); }, "", pybind11::arg("left"), pybind11::arg("right"));
	M("Create").def("mod_signed", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::mod_signed, "Create an Expr with an Mod op\n  Expr pointers may not be nullptr\n\nC++: Create::mod_signed(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("d"));

	// Create::mod_unsigned(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:208
	M("Create").def("mod_unsigned", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1) -> std::shared_ptr<const class Expr::Base> { return Create::mod_unsigned(a0, a1); }, "", pybind11::arg("left"), pybind11::arg("right"));
	M("Create").def("mod_unsigned", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::mod_unsigned, "Create an Expr with an Mod op\n  Expr pointers may not be nullptr\n\nC++: Create::mod_unsigned(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("d"));

	// Create::shift_l(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:227
	M("Create").def("shift_l", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1) -> std::shared_ptr<const class Expr::Base> { return Create::shift_l(a0, a1); }, "", pybind11::arg("left"), pybind11::arg("right"));
	M("Create").def("shift_l", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::shift_l, "A shortcut for shift<ShiftLeft>; exists for the API \n\nC++: Create::shift_l(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("d"));

	// Create::shift_arithmetic_right(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:233
	M("Create").def("shift_arithmetic_right", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1) -> std::shared_ptr<const class Expr::Base> { return Create::shift_arithmetic_right(a0, a1); }, "", pybind11::arg("left"), pybind11::arg("right"));
	M("Create").def("shift_arithmetic_right", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::shift_arithmetic_right, "A shortcut for shift<ShiftArithmeticRight>; exists for the API \n\nC++: Create::shift_arithmetic_right(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("d"));

	// Create::shift_logical_right(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:239
	M("Create").def("shift_logical_right", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1) -> std::shared_ptr<const class Expr::Base> { return Create::shift_logical_right(a0, a1); }, "", pybind11::arg("left"), pybind11::arg("right"));
	M("Create").def("shift_logical_right", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::shift_logical_right, "A shortcut for shift<ShiftLogicalRight>; exists for the API \n\nC++: Create::shift_logical_right(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("d"));

	// Create::rotate_left(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:247
	M("Create").def("rotate_left", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1) -> std::shared_ptr<const class Expr::Base> { return Create::rotate_left(a0, a1); }, "", pybind11::arg("left"), pybind11::arg("right"));
	M("Create").def("rotate_left", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::rotate_left, "Create an Expr with a RotateLeft op\n  Expr pointers may not be nullptr\n\nC++: Create::rotate_left(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("d"));

	// Create::rotate_right(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:256
	M("Create").def("rotate_right", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1) -> std::shared_ptr<const class Expr::Base> { return Create::rotate_right(a0, a1); }, "", pybind11::arg("left"), pybind11::arg("right"));
	M("Create").def("rotate_right", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::rotate_right, "Create an Expr with a RotateRight op\n  Expr pointers may not be nullptr\n\nC++: Create::rotate_right(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("d"));

	// Create::widen(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:268
	M("Create").def("widen", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1) -> std::shared_ptr<const class Expr::Base> { return Create::widen(a0, a1); }, "", pybind11::arg("left"), pybind11::arg("right"));
	M("Create").def("widen", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::widen, "Create an Expr with an Widen op\n  Expr pointers may not be nullptr\n\nC++: Create::widen(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("d"));

	// Create::union_(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:277
	M("Create").def("union_", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1) -> std::shared_ptr<const class Expr::Base> { return Create::union_(a0, a1); }, "", pybind11::arg("left"), pybind11::arg("right"));
	M("Create").def("union_", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::union_, "Create an Expr with an Union op\n  Expr pointers may not be nullptr\n\nC++: Create::union_(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("d"));

	// Create::intersection_(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) file: line:286
	M("Create").def("intersection_", [](const class std::shared_ptr<const class Expr::Base> & a0, const class std::shared_ptr<const class Expr::Base> & a1) -> std::shared_ptr<const class Expr::Base> { return Create::intersection_(a0, a1); }, "", pybind11::arg("left"), pybind11::arg("right"));
	M("Create").def("intersection_", (class std::shared_ptr<const class Expr::Base> (*)(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>)) &Create::intersection_, "Create an Expr with an Intersection op\n  Expr pointers may not be nullptr\n\nC++: Create::intersection_(const class std::shared_ptr<const class Expr::Base> &, const class std::shared_ptr<const class Expr::Base> &, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("left"), pybind11::arg("right"), pybind11::arg("d"));

	// Create::concat(class std::vector<class std::shared_ptr<const class Expr::Base> >, class std::optional<class pybind11::dict>) file: line:299
	M("Create").def("concat", [](class std::vector<class std::shared_ptr<const class Expr::Base> > const & a0) -> std::shared_ptr<const class Expr::Base> { return Create::concat(a0); }, "", pybind11::arg("operands"));
	M("Create").def("concat", (class std::shared_ptr<const class Expr::Base> (*)(class std::vector<class std::shared_ptr<const class Expr::Base> >, class std::optional<class pybind11::dict>)) &Create::concat, "Create an Expr with an Concat op\n  Expr pointers may not be nullptr\n\nC++: Create::concat(class std::vector<class std::shared_ptr<const class Expr::Base> >, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("operands"), pybind11::arg("d"));

	// Create::add(class std::vector<class std::shared_ptr<const class Expr::Base> >, class std::optional<class pybind11::dict>) file: line:309
	M("Create").def("add", [](class std::vector<class std::shared_ptr<const class Expr::Base> > const & a0) -> std::shared_ptr<const class Expr::Base> { return Create::add(a0); }, "", pybind11::arg("operands"));
	M("Create").def("add", (class std::shared_ptr<const class Expr::Base> (*)(class std::vector<class std::shared_ptr<const class Expr::Base> >, class std::optional<class pybind11::dict>)) &Create::add, "Create an Expr with an Add op\n  Expr pointers may not be nullptr\n\nC++: Create::add(class std::vector<class std::shared_ptr<const class Expr::Base> >, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("operands"), pybind11::arg("d"));

	// Create::mul(class std::vector<class std::shared_ptr<const class Expr::Base> >, class std::optional<class pybind11::dict>) file: line:317
	M("Create").def("mul", [](class std::vector<class std::shared_ptr<const class Expr::Base> > const & a0) -> std::shared_ptr<const class Expr::Base> { return Create::mul(a0); }, "", pybind11::arg("operands"));
	M("Create").def("mul", (class std::shared_ptr<const class Expr::Base> (*)(class std::vector<class std::shared_ptr<const class Expr::Base> >, class std::optional<class pybind11::dict>)) &Create::mul, "Create an Expr with an Mul op\n  Expr pointers may not be nullptr\n\nC++: Create::mul(class std::vector<class std::shared_ptr<const class Expr::Base> >, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("operands"), pybind11::arg("d"));

	// Create::or_(class std::vector<class std::shared_ptr<const class Expr::Base> >, class std::optional<class pybind11::dict>) file: line:327
	M("Create").def("or_", [](class std::vector<class std::shared_ptr<const class Expr::Base> > const & a0) -> std::shared_ptr<const class Expr::Base> { return Create::or_(a0); }, "", pybind11::arg("operands"));
	M("Create").def("or_", (class std::shared_ptr<const class Expr::Base> (*)(class std::vector<class std::shared_ptr<const class Expr::Base> >, class std::optional<class pybind11::dict>)) &Create::or_, "Create an Expr with an Or op\n  Expr pointers may not be nullptr\n\nC++: Create::or_(class std::vector<class std::shared_ptr<const class Expr::Base> >, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("operands"), pybind11::arg("d"));

}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_37.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_37(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	// Create::and_(class std::vector<class std::shared_ptr<const class Expr::Base> >, class std::optional<class pybind11::dict>) file: line:334
	M("Create").def("and_", [](class std::vector<class std::shared_ptr<const class Expr::Base> > const & a0) -> std::shared_ptr<const class Expr::Base> { return Create::and_(a0); }, "", pybind11::arg("operands"));
	M("Create").def("and_", (class std::shared_ptr<const class Expr::Base> (*)(class std::vector<class std::shared_ptr<const class Expr::Base> >, class std::optional<class pybind11::dict>)) &Create::and_, "Create an Expr with an And op\n  Expr pointers may not be nullptr\n\nC++: Create::and_(class std::vector<class std::shared_ptr<const class Expr::Base> >, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("operands"), pybind11::arg("d"));

	// Create::xor_(class std::vector<class std::shared_ptr<const class Expr::Base> >, class std::optional<class pybind11::dict>) file: line:341
	M("Create").def("xor_", [](class std::vector<class std::shared_ptr<const class Expr::Base> > const & a0) -> std::shared_ptr<const class Expr::Base> { return Create::xor_(a0); }, "", pybind11::arg("operands"));
	M("Create").def("xor_", (class std::shared_ptr<const class Expr::Base> (*)(class std::vector<class std::shared_ptr<const class Expr::Base> >, class std::optional<class pybind11::dict>)) &Create::xor_, "Create an Expr with an Xor op\n  Expr pointers may not be nullptr\n\nC++: Create::xor_(class std::vector<class std::shared_ptr<const class Expr::Base> >, class std::optional<class pybind11::dict>) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("operands"), pybind11::arg("d"));

}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_38.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_38(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	{ // Backend::Z3::Solver file: line:13
		pybind11::class_<Backend::Z3::Solver, std::shared_ptr<Backend::Z3::Solver>> cl(M("Backend::Z3"), "Solver", "A Z3 Solver object " );
		cl.def( pybind11::init( [](Backend::Z3::Solver const &o){ return new Backend::Z3::Solver(o); } ) );
		cl.def("assign", (class Backend::Z3::Solver & (Backend::Z3::Solver::*)(const class Backend::Z3::Solver &)) &Backend::Z3::Solver::operator=, "C++: Backend::Z3::Solver::operator=(const class Backend::Z3::Solver &) --> class Backend::Z3::Solver &", pybind11::return_value_policy::automatic, pybind11::arg(""));

		cl.def("__str__", [](Backend::Z3::Solver const &o) -> std::string { std::ostringstream s; s << o; return s.str(); } );
	}
}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_39.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_39(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	{ // Backend::Z3::Z3 file: line:24
		pybind11::class_<Backend::Z3::Z3, std::shared_ptr<Backend::Z3::Z3>> cl(M("Backend::Z3"), "Z3", "The Z3 backend\n  Warning: All Z3 backends within a given thread share their data" );
		cl.def( pybind11::init( [](){ return new Backend::Z3::Z3(); } ) );
		cl.def("name", (const char * (Backend::Z3::Z3::*)() const) &Backend::Z3::Z3::name, "The name of this backend \n\nC++: Backend::Z3::Z3::name() const --> const char *", pybind11::return_value_policy::automatic);
		cl.def("simplify", (class std::shared_ptr<const class Expr::Base> (Backend::Z3::Z3::*)(const class Expr::Base *const)) &Backend::Z3::Z3::simplify, "Simplify the given expr\n  expr may not be nullptr\n\nC++: Backend::Z3::Z3::simplify(const class Expr::Base *const) --> class std::shared_ptr<const class Expr::Base>", pybind11::arg("expr"));
		cl.def("clear_persistent_data", (void (Backend::Z3::Z3::*)()) &Backend::Z3::Z3::clear_persistent_data, "Clears translocation data \n\nC++: Backend::Z3::Z3::clear_persistent_data() --> void");
		cl.def("satisfiable", (bool (Backend::Z3::Z3::*)(class Backend::Z3::Solver &) const) &Backend::Z3::Z3::satisfiable, "Check to see if the solver is in a satisfiable state \n\nC++: Backend::Z3::Z3::satisfiable(class Backend::Z3::Solver &) const --> bool", pybind11::arg("solver"));
		cl.def("satisfiable", (bool (Backend::Z3::Z3::*)(class Backend::Z3::Solver &, const class std::vector<const class Expr::Base *> &)) &Backend::Z3::Z3::satisfiable, "Check to see if the solver is in a satisfiable state \n\nC++: Backend::Z3::Z3::satisfiable(class Backend::Z3::Solver &, const class std::vector<const class Expr::Base *> &) --> bool", pybind11::arg("solver"), pybind11::arg("extra_constraints"));
		cl.def("solution", (bool (Backend::Z3::Z3::*)(const class Expr::Base *const, const class Expr::Base *const, class Backend::Z3::Solver &, const class std::vector<const class Expr::Base *> &)) &Backend::Z3::Z3::solution, "Check if expr = sol is a solution to the given solver; none may be nullptr \n\nC++: Backend::Z3::Z3::solution(const class Expr::Base *const, const class Expr::Base *const, class Backend::Z3::Solver &, const class std::vector<const class Expr::Base *> &) --> bool", pybind11::arg("expr"), pybind11::arg("sol"), pybind11::arg("solver"), pybind11::arg("extra_constraints"));
		cl.def("solution", (bool (Backend::Z3::Z3::*)(const class Expr::Base *const, const class Expr::Base *const, class Backend::Z3::Solver &)) &Backend::Z3::Z3::solution, "Check to see if sol is a solution to expr w.r.t the solver; neither may be nullptr \n\nC++: Backend::Z3::Z3::solution(const class Expr::Base *const, const class Expr::Base *const, class Backend::Z3::Solver &) --> bool", pybind11::arg("expr"), pybind11::arg("sol"), pybind11::arg("solver"));
		cl.def("unsat_core", (class std::vector<class std::shared_ptr<const class Expr::Base> > (Backend::Z3::Z3::*)(const class Backend::Z3::Solver &)) &Backend::Z3::Z3::unsat_core, "Return the unsat core from the solver\n  Warning: This assumes all of solver->assertions were added by add<true>\n\nC++: Backend::Z3::Z3::unsat_core(const class Backend::Z3::Solver &) --> class std::vector<class std::shared_ptr<const class Expr::Base> >", pybind11::arg("solver"));
		cl.def("eval", (class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt> > (Backend::Z3::Z3::*)(const class Expr::Base *const, class Backend::Z3::Solver &, const unsigned long long)) &Backend::Z3::Z3::eval, "Evaluate expr, return up to n different solutions\n  No pointers may be nullptr\n\nC++: Backend::Z3::Z3::eval(const class Expr::Base *const, class Backend::Z3::Solver &, const unsigned long long) --> class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt> >", pybind11::arg("expr"), pybind11::arg("solver"), pybind11::arg("n_sol"));
		cl.def("eval", (class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt> > (Backend::Z3::Z3::*)(const class Expr::Base *const, class Backend::Z3::Solver &, const unsigned long long, const class std::vector<const class Expr::Base *> &)) &Backend::Z3::Z3::eval, "Evaluate expr, return up to n different solutions\n  No pointers may be nullptr\n\nC++: Backend::Z3::Z3::eval(const class Expr::Base *const, class Backend::Z3::Solver &, const unsigned long long, const class std::vector<const class Expr::Base *> &) --> class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt> >", pybind11::arg("expr"), pybind11::arg("s"), pybind11::arg("n"), pybind11::arg("extra_constraints"));
		cl.def("batch_eval", (class std::vector<class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt> > > (Backend::Z3::Z3::*)(const class std::vector<const class Expr::Base *> &, class Backend::Z3::Solver &, const unsigned long long)) &Backend::Z3::Z3::batch_eval, "Evaluate every expr, return up to n different solutions\n  No pointers may be nullptr\n\nC++: Backend::Z3::Z3::batch_eval(const class std::vector<const class Expr::Base *> &, class Backend::Z3::Solver &, const unsigned long long) --> class std::vector<class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt> > >", pybind11::arg("exprs"), pybind11::arg("s"), pybind11::arg("n"));
		cl.def("batch_eval", (class std::vector<class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt> > > (Backend::Z3::Z3::*)(const class std::vector<const class Expr::Base *> &, class Backend::Z3::Solver &, const unsigned long long, const class std::vector<const class Expr::Base *> &)) &Backend::Z3::Z3::batch_eval, "Evaluate every expr, return up to n different solutions\n  No pointers may be nullptr\n\nC++: Backend::Z3::Z3::batch_eval(const class std::vector<const class Expr::Base *> &, class Backend::Z3::Solver &, const unsigned long long, const class std::vector<const class Expr::Base *> &) --> class std::vector<class std::vector<class std::variant<bool, std::string, float, double, class std::shared_ptr<const class PyObj::VS>, unsigned char, unsigned short, unsigned int, unsigned long long, struct BigInt> > >", pybind11::arg("exprs"), pybind11::arg("s"), pybind11::arg("n"), pybind11::arg("extra_constraints"));
	}
}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_4.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_4(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	// Mode::BigInt file: line:13
	pybind11::enum_<Mode::BigInt>(M("Mode"), "BigInt", "A mask used to define the type of comparison to be used ")
		.value("Str", Mode::BigInt::Str)
		.value("Int", Mode::BigInt::Int);

;

}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_5.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_5(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	// Mode::FP::Rounding file: line:14
	pybind11::enum_<Mode::FP::Rounding>(M("Mode::FP"), "Rounding", "FP modes supported by claripy ")
		.value("NearestTiesEven", Mode::FP::Rounding::NearestTiesEven)
		.value("NearestTiesAwayFromZero", Mode::FP::Rounding::NearestTiesAwayFromZero)
		.value("TowardsZero", Mode::FP::Rounding::TowardsZero)
		.value("TowardsPositiveInf", Mode::FP::Rounding::TowardsPositiveInf)
		.value("TowardsNegativeInf", Mode::FP::Rounding::TowardsNegativeInf);

;

	{ // Mode::FP::Width file: line:17
		pybind11::class_<Mode::FP::Width, std::shared_ptr<Mode::FP::Width>> cl(M("Mode::FP"), "Width", "A floating point width struct " );
		cl.def( pybind11::init( [](){ return new Mode::FP::Width(); } ) );
		cl.def( pybind11::init( [](Mode::FP::Width const &o){ return new Mode::FP::Width(o); } ) );
		cl.def_readwrite("exp", &Mode::FP::Width::exp);
		cl.def_readwrite("mantissa", &Mode::FP::Width::mantissa);
		cl.def("mantissa_raw", (unsigned int (Mode::FP::Width::*)() const) &Mode::FP::Width::mantissa_raw, "The width of the mantissa, excluding the implicit 1 bit \n\nC++: Mode::FP::Width::mantissa_raw() const --> unsigned int");
		cl.def("width", (unsigned long long (Mode::FP::Width::*)() const) &Mode::FP::Width::width, "The full width of the fp \n\nC++: Mode::FP::Width::width() const --> unsigned long long");
		cl.def("no_sign_width", (unsigned long long (Mode::FP::Width::*)() const) &Mode::FP::Width::no_sign_width, "The full width of the fp \n\nC++: Mode::FP::Width::no_sign_width() const --> unsigned long long");
		cl.def("__eq__", (bool (Mode::FP::Width::*)(const struct Mode::FP::Width &) const) &Mode::FP::Width::operator==, "Equality operator\n  Note: This is internal to the class for API generation reasons\n\nC++: Mode::FP::Width::operator==(const struct Mode::FP::Width &) const --> bool", pybind11::arg("b"));
		cl.def("assign", (struct Mode::FP::Width & (Mode::FP::Width::*)(const struct Mode::FP::Width &)) &Mode::FP::Width::operator=, "C++: Mode::FP::Width::operator=(const struct Mode::FP::Width &) --> struct Mode::FP::Width &", pybind11::return_value_policy::automatic, pybind11::arg(""));

		cl.def("__str__", [](Mode::FP::Width const &o) -> std::string { std::ostringstream s; s << o; return s.str(); } );
	}
}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_6.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_6(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	// Mode::Sign::FP file: line:17
	pybind11::enum_<Mode::Sign::FP>(M("Mode::Sign"), "FP", "An Sign enum with an underlying signed value where non-signed-ness is disallowed\n  The underlying values of the enum values are 1 and -1\n  signed specifier is required for cross-platform support")
		.value("Minus", Mode::Sign::FP::Minus)
		.value("Plus", Mode::Sign::FP::Plus);

;

	// Mode::Sign::Real file: line:23
	pybind11::enum_<Mode::Sign::Real>(M("Mode::Sign"), "Real", "An Sign enum with an underlying signed value where non-signed-ness is allowed\n  The underlying values of the enum values are 1, -1, and 0\n  signed specifier is required for cross-platform support")
		.value("Minus", Mode::Sign::Real::Minus)
		.value("None", Mode::Sign::Real::None)
		.value("Plus", Mode::Sign::Real::Plus);

;

	// Mode::Sign::to_real(const enum Mode::Sign::FP) file: line:26
	M("Mode::Sign").def("to_real", (enum Mode::Sign::Real (*)(const enum Mode::Sign::FP)) &Mode::Sign::to_real, "Convert an FP to a Real \n\nC++: Mode::Sign::to_real(const enum Mode::Sign::FP) --> enum Mode::Sign::Real", pybind11::arg("f"));

}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_7.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_7(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	{ // BigInt file: line:17
		pybind11::class_<BigInt, std::shared_ptr<BigInt>> cl(M(""), "BigInt", "The arbitrary precision type claricpp uses " );
		cl.def( pybind11::init( [](BigInt const &o){ return new BigInt(o); } ) );
		cl.def( pybind11::init( [](){ return new BigInt(); } ) );
		cl.def_readwrite("value", &BigInt::value);
		cl.def_readwrite("bit_length", &BigInt::bit_length);
		cl.def_static("from_c_str", (struct BigInt (*)(const char *const, const unsigned long long)) &BigInt::from_c_str<Mode::BigInt::Str>, "C++: BigInt::from_c_str(const char *const, const unsigned long long) --> struct BigInt", pybind11::arg("s"), pybind11::arg("bit_length"));
		cl.def_static("from_c_str", (struct BigInt (*)(const char *const, const unsigned long long)) &BigInt::from_c_str<Mode::BigInt::Int>, "C++: BigInt::from_c_str(const char *const, const unsigned long long) --> struct BigInt", pybind11::arg("s"), pybind11::arg("bit_length"));
		cl.def_static("from_c_str", (struct BigInt (*)(const char *const, const unsigned long long)) &BigInt::from_c_str, "Convert the input to a BigInt using the default mode \n\nC++: BigInt::from_c_str(const char *const, const unsigned long long) --> struct BigInt", pybind11::arg("s"), pybind11::arg("bit_length"));
		cl.def_static("mode", (enum Mode::BigInt (*)(const enum Mode::BigInt)) &BigInt::mode, "Set the default BigInt mode to m \n\nC++: BigInt::mode(const enum Mode::BigInt) --> enum Mode::BigInt", pybind11::arg("m"));
		cl.def_static("mode", (enum Mode::BigInt (*)()) &BigInt::mode, "Get the default mode \n\nC++: BigInt::mode() --> enum Mode::BigInt");
		cl.def("__eq__", (bool (BigInt::*)(const struct BigInt &) const) &BigInt::operator==, "Equality operator\n  Note: This is internal to the class for API generation reasons\n\nC++: BigInt::operator==(const struct BigInt &) const --> bool", pybind11::arg("b"));
		cl.def("assign", (struct BigInt & (BigInt::*)(const struct BigInt &)) &BigInt::operator=, "C++: BigInt::operator=(const struct BigInt &) --> struct BigInt &", pybind11::return_value_policy::automatic, pybind11::arg(""));

		cl.def("__str__", [](BigInt const &o) -> std::string { std::ostringstream s; s << o; return s.str(); } );
	}
}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_8.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_8(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	// Hash::serialize(const class std::shared_ptr<const class Expr::Base> &) file: line:40
	M("Hash").def("serialize", (unsigned long long (*)(const class std::shared_ptr<const class Expr::Base> &)) &Hash::serialize<const Expr::Base>, "C++: Hash::serialize(const class std::shared_ptr<const class Expr::Base> &) --> unsigned long long", pybind11::arg(""));

	// Hash::serialize(const class std::shared_ptr<const class Op::Base> &) file: line:40
	M("Hash").def("serialize", (unsigned long long (*)(const class std::shared_ptr<const class Op::Base> &)) &Hash::serialize<const Op::Base>, "C++: Hash::serialize(const class std::shared_ptr<const class Op::Base> &) --> unsigned long long", pybind11::arg(""));

	// Hash::serialize(const class std::shared_ptr<const class PyObj::VS> &) file: line:40
	M("Hash").def("serialize", (unsigned long long (*)(const class std::shared_ptr<const class PyObj::VS> &)) &Hash::serialize<const PyObj::VS>, "C++: Hash::serialize(const class std::shared_ptr<const class PyObj::VS> &) --> unsigned long long", pybind11::arg(""));

	// Hash::serialize(const struct Mode::FP::Width &) file: line:148
	M("Hash").def("serialize", (unsigned long long (*)(const struct Mode::FP::Width &)) &Hash::serialize<Mode::FP::Width>, "A specialization for T = Mode::FP::Width \n\nC++: Hash::serialize(const struct Mode::FP::Width &) --> unsigned long long", pybind11::arg("w"));

	// Hash::serialize(const class std::shared_ptr<const class Expr::Base> &) file: line:206
	M("Hash").def("serialize", (unsigned long long (*)(const class std::shared_ptr<const class Expr::Base> &)) &Hash::serialize<Expr::Base>, "C++: Hash::serialize(const class std::shared_ptr<const class Expr::Base> &) --> unsigned long long", pybind11::arg("p"));

	// Hash::serialize(const class std::shared_ptr<const class Op::Base> &) file: line:206
	M("Hash").def("serialize", (unsigned long long (*)(const class std::shared_ptr<const class Op::Base> &)) &Hash::serialize<Op::Base>, "C++: Hash::serialize(const class std::shared_ptr<const class Op::Base> &) --> unsigned long long", pybind11::arg("p"));

	// Hash::serialize(const class std::shared_ptr<const class PyObj::VS> &) file: line:206
	M("Hash").def("serialize", (unsigned long long (*)(const class std::shared_ptr<const class PyObj::VS> &)) &Hash::serialize<PyObj::VS>, "C++: Hash::serialize(const class std::shared_ptr<const class PyObj::VS> &) --> unsigned long long", pybind11::arg("p"));

}
} // namespace API::Binder


//
// File: binder/raw_output/unknown/unknown_9.cpp
//


#ifndef BINDER_PYBIND11_TYPE_CASTER
	#define BINDER_PYBIND11_TYPE_CASTER
	PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
	PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
	PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif

namespace API::Binder {
void bind_unknown_unknown_9(std::function< pybind11::module &(std::string const &namespace_) > &M)
{
	// Hash::Private::type_id() file: line:18
	M("Hash::Private").def("type_id", (unsigned long long (*)()) &Hash::Private::type_id<Expr::Base>, "C++: Hash::Private::type_id() --> unsigned long long");

	// Hash::Private::type_id() file: line:18
	M("Hash::Private").def("type_id", (unsigned long long (*)()) &Hash::Private::type_id<Op::Base>, "C++: Hash::Private::type_id() --> unsigned long long");

	// Hash::Private::type_id() file: line:18
	M("Hash::Private").def("type_id", (unsigned long long (*)()) &Hash::Private::type_id<PyObj::VS>, "C++: Hash::Private::type_id() --> unsigned long long");

}
} // namespace API::Binder