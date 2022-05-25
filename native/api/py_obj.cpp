/**
 * @file
 * \ingroup api
 */
#include "py_obj.hpp"

#include "err.hpp"

#include <src/py_obj.hpp>


/** A class which derives a PyObj and adds pybind11 machinery */
template <typename Base> class PyO final : public Base {
  public:
    /** Constructor */
    inline PyO(pybind11::object &&py, const U64 bit_length)
        : Base { Util::unsign(pybind11::hash(py)), bit_length }, rep { std::move(py) } {
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

void API::py_obj(Binder::ModuleGetter &m) {
    auto p_o { m("API").def_submodule("py_obj_ctor", "PyObj ctors") };
    p_o.def(
        "bvvs",
        [](pybind11::object &&obj, const U64 bit_length) {
            return static_cast<const PyObj::BVVS *>(
                new PyO<PyObj::BVVS> { std::move(obj), bit_length });
        },
        "Create a C++ wrapper of type PyObj::BVVS for the python object o", pybind11::arg("obj"),
        pybind11::arg("bit_length"), pybind11::return_value_policy::take_ownership);
}