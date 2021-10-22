/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"


/** Test normal ops in claricpp
 *  @todo: Enable string symbol testing
 */
void normal() {
    namespace Ex = Expr;
    namespace C = Create;

    // The backend
    Backend::Z3::Z3 z3bk;

    /* const auto string_x { C::symbol<Ex::String>("string_x", 64_ui) }; */
    /* const auto string_y { C::symbol<Ex::String>("string_y", 64_ui) }; */
    const auto fp_x { C::symbol<Ex::FP>("fp_x", Mode::FP::dbl.width()) };
    const auto fp_y { C::symbol<Ex::FP>("fp_y", Mode::FP::dbl.width()) };
    const auto bv_x { C::symbol<Ex::BV>("bv_x", 64_ui) };
    const auto bv_y { C::symbol<Ex::BV>("bv_y", 64_ui) };
    const auto bool_x { C::symbol("bool_x") };
    const auto bool_y { C::symbol("bool_y") };

    // Verify the round trip changes nothing
    const auto test_id = [&z3bk](const Expr::BasePtr &&x) {
        return z3bk.abstract(z3bk.convert(x.get())) == x;
    };

    /**************************************************/
    /*                  Non-Trivial                   */
    /**************************************************/

    Util::Log::debug("Testing if...");
    UNITTEST_ASSERT(test_id(C::if_(bool_x, bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(C::if_(bool_x, fp_x, fp_y)));
    UNITTEST_ASSERT(test_id(C::if_(bool_x, bool_x, bool_y)));
    /* UNITTEST_ASSERT(test_id(C::if_(bool_x, string_x, string_y))); */

    Util::Log::debug("Testing extract...");
    UNITTEST_ASSERT(test_id(C::extract(2, 1, bv_x)));

    Util::Log::debug("Testing literal...");
    UNITTEST_ASSERT(test_id(C::literal(true)));
    UNITTEST_ASSERT(test_id(C::literal(1.)));
    UNITTEST_ASSERT(test_id(C::literal(1.F)));
    /* UNITTEST_ASSERT(test_id(C::literal(std::string("Hello")))); */

    UNITTEST_ASSERT(test_id(C::literal(uint8_t { 2 })));
    UNITTEST_ASSERT(test_id(C::literal(uint16_t { 2 })));
    UNITTEST_ASSERT(test_id(C::literal(uint32_t { 2 })));
    UNITTEST_ASSERT(test_id(C::literal(uint64_t { 2 })));

    Util::Log::debug("Testing symbol...");
    UNITTEST_ASSERT(bool_x);
    UNITTEST_ASSERT(bv_x);
    UNITTEST_ASSERT(fp_x);
    /* UNITTEST_ASSERT(string_x); */

    /**************************************************/
    /*                    Trivial                     */
    /**************************************************/

    // Unary

    Util::Log::debug("Testing abs...");
    UNITTEST_ASSERT(test_id(C::abs(fp_x)));

    Util::Log::debug("Testing not...");
    UNITTEST_ASSERT(test_id(C::not_(bool_x)));

    Util::Log::debug("Testing invert...");
    UNITTEST_ASSERT(test_id(C::invert(bv_x)));

    Util::Log::debug("Testing neg...");
    UNITTEST_ASSERT(test_id(C::neg(fp_x)));
    UNITTEST_ASSERT(test_id(C::neg(bv_x)));

    Util::Log::debug("Testing reverse...");
    const auto also_x { C::reverse(C::reverse(bv_x)) };
    UNITTEST_ASSERT(z3bk.simplify(also_x.get()) == bv_x);


    // UInt Binary

    Util::Log::debug("Testing signext...");
    UNITTEST_ASSERT(test_id(C::sign_ext(bv_x, 1)));

    Util::Log::debug("Testing zeroext...");
    UNITTEST_ASSERT(test_id(C::zero_ext(bv_x, 1)));


    // Binary

    Util::Log::debug("Testing eq...");
    UNITTEST_ASSERT(test_id(C::eq(fp_x, fp_y)));
    UNITTEST_ASSERT(test_id(C::eq(bool_x, bool_y)));
    /* UNITTEST_ASSERT(test_id(C::eq<Ex::String>(string_x, string_y))); */

    Util::Log::debug("Testing neq...");
    UNITTEST_ASSERT(test_id(C::neq(fp_x, fp_y)));
    UNITTEST_ASSERT(test_id(C::neq(bool_x, bool_y)));
    /* UNITTEST_ASSERT(test_id(C::neq<Ex::String>(string_x, string_y))); */

    using Cmp = Mode::Compare;
    Util::Log::debug("Testing compare...");
    const auto sl { Cmp::Signed | Cmp::Less };
    const auto sg { Cmp::Signed | Cmp::Less };
    UNITTEST_ASSERT(test_id(C::compare<sl | Cmp::Eq>(fp_x, fp_y)));
    UNITTEST_ASSERT(test_id(C::compare<sl | Cmp::Neq>(fp_x, fp_y)));
    UNITTEST_ASSERT(test_id(C::compare<sg | Cmp::Eq>(fp_x, fp_y)));
    UNITTEST_ASSERT(test_id(C::compare<sg | Cmp::Neq>(fp_x, fp_y)));

    UNITTEST_ASSERT(test_id(C::compare<sl | Cmp::Eq>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(C::compare<sl | Cmp::Neq>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(C::compare<sg | Cmp::Eq>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(C::compare<sg | Cmp::Neq>(bv_x, bv_y)));
    const auto ul { Cmp::Unsigned | Cmp::Less };
    const auto ug { Cmp::Unsigned | Cmp::Less };
    UNITTEST_ASSERT(test_id(C::compare<ul | Cmp::Eq>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(C::compare<ul | Cmp::Neq>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(C::compare<ug | Cmp::Eq>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(C::compare<ug | Cmp::Neq>(bv_x, bv_y)));

    Util::Log::debug("Testing sub...");
    UNITTEST_ASSERT(test_id(C::sub(bv_x, bv_y)));

    Util::Log::debug("Testing div...");
    UNITTEST_ASSERT(test_id(C::div<true>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(C::div<false>(bv_x, bv_y)));

    Util::Log::debug("Testing mod...");
    UNITTEST_ASSERT(test_id(C::mod<true>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(C::mod<false>(bv_x, bv_y)));

    using M = Mode::Shift;
    Util::Log::debug("Testing shift...");
    UNITTEST_ASSERT(test_id(C::shift<M::Left>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(C::shift<M::LogicalRight>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(C::shift<M::ArithmeticRight>(bv_x, bv_y)));

    using LR = Mode::LR;
    Util::Log::debug("Testing rotate...");
    UNITTEST_ASSERT(test_id(C::rotate<LR::Left>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(C::rotate<LR::Right>(bv_x, bv_y)));

    Util::Log::debug("Testing concat...");
    UNITTEST_ASSERT(test_id(C::concat(bv_x, bv_y)));
    /* UNITTEST_ASSERT(test_id(C::concat<Ex::String>(string_x, string_y))); */

    // Flat

    Util::Log::debug("Testing add...");
    UNITTEST_ASSERT(test_id(C::add({ bv_x, bv_y })));

    Util::Log::debug("Testing mul...");
    UNITTEST_ASSERT(test_id(C::mul({ bv_x, bv_y })));

    Util::Log::debug("Testing or...");
    UNITTEST_ASSERT(test_id(C::or_({ bv_x, bv_y })));
    UNITTEST_ASSERT(test_id(C::or_({ bool_x, bool_y })));

    Util::Log::debug("Testing and...");
    UNITTEST_ASSERT(test_id(C::and_({ bv_x, bv_y })));
    UNITTEST_ASSERT(test_id(C::and_({ bool_x, bool_y })));

    Util::Log::debug("Testing xor...");
    UNITTEST_ASSERT(test_id(C::xor_({ bv_x, bv_y })));
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(normal)
