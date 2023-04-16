/**
 * @file
 * \ingroup api
 */
#include "py_obj.hpp"

#include "err.hpp"

#include "../py_obj.hpp"


/** A class which derives a PyObj and adds pybind11 machinery */
template <typename Base> class PyO final : public Base {
  public:
    /** Constructor */
    inline PyO(pybind11::object &&py, const U64 bit_len)
        : Base { Util::unsign(pybind11::hash(py)), bit_len }, rep { std::move(py) } {
        const bool has_repr { pybind11::hasattr(std::get<pybind11::object>(rep), "__repr__") };
        UTIL_ASSERT(API::Err::Usage, has_repr, "Python Object must have __repr__ defined");
    }

  protected:
    /** Override for actual repr */
    inline std::string actual_repr() const final {
        if (std::holds_alternative<pybind11::object>(rep)) {
            // Note: we are explicit in noting std::string as repr returns a python string
            rep = std::string { pybind11::repr(std::get<pybind11::object>(rep)) };
        }
        return std::get<std::string>(rep);
    }
    /** Representation */
    mutable std::variant<std::string, pybind11::object> rep;
};

template <typename T> static void py_o(pybind11::module_ &m, CCSC name) {
    static_assert(std::is_base_of_v<PyObj::Base, T>, "Usage");
    std::ostringstream doc;
    doc << "Create a C++ wrapper of type " << name << " for the python object o";
    m.def(
        name,
        [](pybind11::object &&obj, const U64 bit_length) {
            return static_cast<const T *>(new PyO<T> { std::move(obj), bit_length });
        },
        doc.str().c_str(), pybind11::arg("obj"), pybind11::arg("bit_length"),
        pybind11::return_value_policy::take_ownership);
}

void API::py_obj(Binder::ModuleGetter &m) {
    // TODO: determine if some register_at_exit function needs to kill py obj references
    auto p_o { m("API").def_submodule("py_obj_ctor", "PyObj ctors") };
    py_o<PyObj::VS>(p_o, "vs");
}
