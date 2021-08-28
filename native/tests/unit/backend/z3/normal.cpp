/**
 * @file
 * \ingroup unittest
 */
#include "backend.hpp"
#include "testlib.hpp"


/** Test normal ops in claricpp
 *  @todo: Enable string symbol testing
 */
void normal() {
    namespace Ex = Expression;
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
    const auto test_id = [&z3bk](const Expression::BasePtr &&x) {
        return z3bk.abstract(z3bk.convert(x.get())) == x;
    };

    /**************************************************/
    /*                  Non-Trivial                   */
    /**************************************************/

    Utils::Log::debug("Testing if...");
    UNITTEST_ASSERT(test_id(C::if_<Ex::BV>(bool_x, bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(C::if_<Ex::FP>(bool_x, fp_x, fp_y)));
    UNITTEST_ASSERT(test_id(C::if_<Ex::Bool>(bool_x, bool_x, bool_y)));
    /* UNITTEST_ASSERT(test_id(C::if_<Ex::String>(bool_x, string_x, string_y))); */

    Utils::Log::debug("Testing extract...");
    UNITTEST_ASSERT(test_id(C::extract(2, 1, bv_x)));

    Utils::Log::debug("Testing literal...");
    UNITTEST_ASSERT(test_id(C::literal(true)));
    UNITTEST_ASSERT(test_id(C::literal(1.)));
    UNITTEST_ASSERT(test_id(C::literal(1.F)));
    /* UNITTEST_ASSERT(test_id(C::literal(std::string("Hello")))); */

    UNITTEST_ASSERT(test_id(C::literal(uint8_t { 2 })));
    UNITTEST_ASSERT(test_id(C::literal(uint16_t { 2 })));
    UNITTEST_ASSERT(test_id(C::literal(uint32_t { 2 })));
    UNITTEST_ASSERT(test_id(C::literal(uint64_t { 2 })));

    Utils::Log::debug("Testing symbol...");
    UNITTEST_ASSERT(bool_x);
    UNITTEST_ASSERT(bv_x);
    UNITTEST_ASSERT(fp_x);
    /* UNITTEST_ASSERT(string_x); */

    /**************************************************/
    /*                    Trivial                     */
    /**************************************************/

    // Unary

    Utils::Log::debug("Testing abs...");
    UNITTEST_ASSERT(test_id(C::abs(fp_x)));

    Utils::Log::debug("Testing not...");
    UNITTEST_ASSERT(test_id(C::not_(bool_x)));

    Utils::Log::debug("Testing invert...");
    UNITTEST_ASSERT(test_id(C::invert(bv_x)));

    Utils::Log::debug("Testing neg...");
    UNITTEST_ASSERT(test_id(C::neg<Ex::FP>(fp_x)));
    UNITTEST_ASSERT(test_id(C::neg<Ex::BV>(bv_x)));

    Utils::Log::debug("Testing reverse...");
    const auto also_x { C::reverse(C::reverse(bv_x)) };
    UNITTEST_ASSERT(z3bk.simplify(also_x.get()) == bv_x);


    // UInt Binary

    Utils::Log::debug("Testing signext...");
    UNITTEST_ASSERT(test_id(C::sign_ext(bv_x, 1)));

    Utils::Log::debug("Testing zeroext...");
    UNITTEST_ASSERT(test_id(C::zero_ext(bv_x, 1)));


    // Binary

    Utils::Log::debug("Testing eq...");
    UNITTEST_ASSERT(test_id(C::eq<Ex::FP>(fp_x, fp_y)));
    UNITTEST_ASSERT(test_id(C::eq<Ex::Bool>(bool_x, bool_y)));
    /* UNITTEST_ASSERT(test_id(C::eq<Ex::String>(string_x, string_y))); */

    Utils::Log::debug("Testing neq...");
    UNITTEST_ASSERT(test_id(C::neq<Ex::FP>(fp_x, fp_y)));
    UNITTEST_ASSERT(test_id(C::neq<Ex::Bool>(bool_x, bool_y)));
    /* UNITTEST_ASSERT(test_id(C::neq<Ex::String>(string_x, string_y))); */

    using Cmp = Mode::Compare;
    Utils::Log::debug("Testing compare...");
    const auto sl { Cmp::Signed | Cmp::Less };
    const auto sg { Cmp::Signed | Cmp::Less };
    UNITTEST_ASSERT(test_id(C::compare<Ex::FP, sl | Cmp::Eq>(fp_x, fp_y)));
    UNITTEST_ASSERT(test_id(C::compare<Ex::FP, sl | Cmp::Neq>(fp_x, fp_y)));
    UNITTEST_ASSERT(test_id(C::compare<Ex::FP, sg | Cmp::Eq>(fp_x, fp_y)));
    UNITTEST_ASSERT(test_id(C::compare<Ex::FP, sg | Cmp::Neq>(fp_x, fp_y)));

    UNITTEST_ASSERT(test_id(C::compare<Ex::BV, sl | Cmp::Eq>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(C::compare<Ex::BV, sl | Cmp::Neq>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(C::compare<Ex::BV, sg | Cmp::Eq>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(C::compare<Ex::BV, sg | Cmp::Neq>(bv_x, bv_y)));
    const auto ul { Cmp::Unsigned | Cmp::Less };
    const auto ug { Cmp::Unsigned | Cmp::Less };
    UNITTEST_ASSERT(test_id(C::compare<Ex::BV, ul | Cmp::Eq>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(C::compare<Ex::BV, ul | Cmp::Neq>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(C::compare<Ex::BV, ug | Cmp::Eq>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(C::compare<Ex::BV, ug | Cmp::Neq>(bv_x, bv_y)));

    Utils::Log::debug("Testing sub...");
    UNITTEST_ASSERT(test_id(C::sub(bv_x, bv_y)));

    Utils::Log::debug("Testing div...");
    UNITTEST_ASSERT(test_id(C::div<true>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(C::div<false>(bv_x, bv_y)));

    Utils::Log::debug("Testing mod...");
    UNITTEST_ASSERT(test_id(C::mod<true>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(C::mod<false>(bv_x, bv_y)));

    using M = Mode::Shift;
    Utils::Log::debug("Testing shift...");
    UNITTEST_ASSERT(test_id(C::shift<M::Left>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(C::shift<M::LogicalRight>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(C::shift<M::ArithmeticRight>(bv_x, bv_y)));

    using LR = Mode::LR;
    Utils::Log::debug("Testing rotate...");
    UNITTEST_ASSERT(test_id(C::rotate<LR::Left>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(C::rotate<LR::Right>(bv_x, bv_y)));

    Utils::Log::debug("Testing concat...");
    UNITTEST_ASSERT(test_id(C::concat<Ex::BV>(bv_x, bv_y)));
    /* UNITTEST_ASSERT(test_id(C::concat<Ex::String>(string_x, string_y))); */

    // Flat

    Utils::Log::debug("Testing add...");
    UNITTEST_ASSERT(test_id(C::add({ bv_x, bv_y })));

    Utils::Log::debug("Testing mul...");
    UNITTEST_ASSERT(test_id(C::mul({ bv_x, bv_y })));

    Utils::Log::debug("Testing or...");
    UNITTEST_ASSERT(test_id(C::or_<Ex::BV>({ bv_x, bv_y })));
    UNITTEST_ASSERT(test_id(C::or_<Ex::Bool>({ bool_x, bool_y })));

    Utils::Log::debug("Testing and...");
    UNITTEST_ASSERT(test_id(C::and_<Ex::BV>({ bv_x, bv_y })));
    UNITTEST_ASSERT(test_id(C::and_<Ex::Bool>({ bool_x, bool_y })));

    Utils::Log::debug("Testing xor...");
    UNITTEST_ASSERT(test_id(C::xor_({ bv_x, bv_y })));
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(normal)