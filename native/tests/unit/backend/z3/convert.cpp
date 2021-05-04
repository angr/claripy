/**
 * @file
 * \ingroup unittest
 */
#include "backend.hpp"
#include "create.hpp"
#include "testlib.hpp"


/** Construct the ite expression: if (4 == (x * 3)) then "Hello" else y */
auto make_ite() {
    namespace Ex = Expression;
    using AV = Ex::Base::AnVec;
    namespace C = Create;

    const auto flt_size { 64_ui };

    // Symbols
    const auto x { C::symbol<Ex::FP>(AV {}, "x", flt_size) };
    const auto y { C::symbol<Ex::String>(AV {}, "y", flt_size) };

    // Literals
    const auto fp3 { C::literal(AV {}, 3.) };
    const auto fp4 { C::literal(AV {}, 4.) };
    const auto hello { C::literal(AV {}, std::string { "Hello" }) };

    // Composite
    const auto prod { C::FP::mul(AV {}, x, fp3, Mode::FP::NearestTiesEven) };
    const auto eq { C::eq<Ex::FP>(AV {}, fp4, prod) };
    return C::if_<Ex::String>(AV {}, eq, hello, y);
}

/** Try to convert a claricpp expression to z3 */
void convert() {
    const auto ite { make_ite() };
    auto z3 { Backend::Z3::Z3 {} };
    (void) z3.convert(ite.get());
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(convert)
