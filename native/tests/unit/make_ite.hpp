/**
 * @file
 * @brief Define a function used to construct an ITE Expr
 * \ingroup unittest
 */
#ifndef R_UNIT_MAKEITE_HPP_
#define R_UNIT_MAKEITE_HPP_

#include "create.hpp"


/** Construct the ite expr: if (4 == (x * 3)) then str else y */
inline auto make_ite(std::string str) {
    namespace Ex = Expr;
    namespace C = Create;

    // Constants
    const auto len { str.size() };
    const auto flt_size { 64_ui };

    // Symbols
    const auto x { C::symbol<Ex::FP>("x", flt_size) };
    const auto y { C::symbol<Ex::String>("y", C_CHAR_BIT * len) };

    // Literals
    const auto fp3 { C::literal(3.) };
    const auto fp4 { C::literal(4.) };
    const auto hello { C::literal(std::move(str)) };

    // Composite
    const auto prod { C::FP::mul(x, fp3, Mode::FP::Rounding::NearestTiesEven) };
    const auto eq { C::eq<Ex::FP>(fp4, prod) };
    return C::if_<Ex::String>(eq, hello, y);
}


#endif
