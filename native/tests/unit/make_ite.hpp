/**
 * @file
 * @brief Define a function used to construct an ITE Expr
 * \ingroup unittest
 */
#ifndef R_TESTS_UNIT_MAKEITE_HPP_
#define R_TESTS_UNIT_MAKEITE_HPP_

#include <src/create.hpp>


/** Construct the ite expr: if (4 == (x * 3)) then str else y */
inline Expr::BasePtr make_ite(std::string str) {
    namespace C = Create;

    // Constants
    const auto len { str.size() };
    const auto flt_size { 64_ui };

    // Symbols
    const auto x { C::symbol_fp("x", flt_size) };
    const auto y { C::symbol_string("y", len) };

    // Literals
    const auto fp3 { C::literal(3.) };
    const auto fp4 { C::literal(4.) };
    const auto hello { C::literal(std::move(str)) };

    // Composite
    const auto prod { C::FP::mul(x, fp3, Mode::FP::Rounding::NearestTiesEven) };
    const auto eq { C::eq(fp4, prod) };
    return C::if_(eq, hello, y);
}


#endif
