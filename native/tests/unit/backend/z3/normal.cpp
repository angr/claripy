/**
 * @file
 * \ingroup unittest
 */
#include "backend.hpp"
#include "testlib.hpp"

#include <memory>

// For brevity
namespace Ex = Expression;

/** The type of test functions */
using Func = void (*)();

/** List of functions to test */
std::vector<Func> functions {};

/** A macro to define a new test function */
#define ADD_TEST(FNAME)                                                                           \
    void FNAME();                                                                                 \
    UTILS_RUN_STATEMENT_BEFORE_MAIN(functions.push_back(&FNAME));                                 \
    void FNAME()


/** Test normal ops in claricpp
 *  @todo: Enable string symbol testing
 */
void normal() {
    Backend::Z3::Z3 z3bk;

    /* const auto string_x { Create::symbol<Ex::String>("string_x", 64_ui) }; */
    /* const auto string_y { Create::symbol<Ex::String>("string_y", 64_ui) }; */
    const auto fp_x { Create::symbol<Ex::FP>("fp_x", Mode::FP::dbl.width()) };
    const auto fp_y { Create::symbol<Ex::FP>("fp_y", Mode::FP::dbl.width()) };
    const auto bv_x { Create::symbol<Ex::BV>("bv_x", 64_ui) };
    const auto bv_y { Create::symbol<Ex::BV>("bv_y", 64_ui) };
    const auto vs_x { Create::symbol<Ex::VS>("vs_x", 64_ui) };
    const auto vs_y { Create::symbol<Ex::VS>("vs_y", 64_ui) };
    const auto bool_x { Create::symbol("bool_x") };
    const auto bool_y { Create::symbol("bool_y") };

    // Verify the round trip changes nothing
    const auto test_id = [&z3bk](const Expression::BasePtr &&x) {
        return z3bk.abstract(z3bk.convert(x)) == x;
    };

    /**************************************************/
    /*                  Non-Trivial                   */
    /**************************************************/

    Utils::Log::debug("Testing if...");
    UNITTEST_ASSERT(test_id(Create::if_<Ex::BV>(bool_x, bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(Create::if_<Ex::FP>(bool_x, fp_x, fp_y)));
    UNITTEST_ASSERT(test_id(Create::if_<Ex::Bool>(bool_x, bool_x, bool_y)));
    UNITTEST_ASSERT(test_id(Create::if_<Ex::VS>(bool_x, vs_x, vs_y)));
    /* UNITTEST_ASSERT(test_id(Create::if_<Ex::String>(bool_x, string_x, string_y))); */

    Utils::Log::debug("Testing extract...");
    UNITTEST_ASSERT(test_id(Create::extract(2, 1, bv_x)));

    Utils::Log::debug("Testing literal...");
    UNITTEST_ASSERT(test_id(Create::literal(true)));
    UNITTEST_ASSERT(test_id(Create::literal({ 'a', 'b' })));
    UNITTEST_ASSERT(test_id(Create::literal(0.)));
    UNITTEST_ASSERT(test_id(Create::literal(0.F)));
    UNITTEST_ASSERT(test_id(Create::literal(std::string("Hello"))));
    const auto vs_obj { std::make_shared<PyObj::VS>(UTILS_FILE_LINE_HASH, 0, 64_ui) };
    UNITTEST_ASSERT(test_id(Create::literal(vs_obj)));

    Utils::Log::debug("Testing symbol...");
    UNITTEST_ASSERT(bool_x);
    UNITTEST_ASSERT(bv_x);
    UNITTEST_ASSERT(fp_x);
    UNITTEST_ASSERT(vs_x);
    /* UNITTEST_ASSERT(string_x); */

    /**************************************************/
    /*                    Trivial                     */
    /**************************************************/

    // Unary

    Utils::Log::debug("Testing abs...");
    UNITTEST_ASSERT(test_id(Create::abs(fp_x)));

    Utils::Log::debug("Testing not...");
    UNITTEST_ASSERT(test_id(Create::not_(bool_x)));

    Utils::Log::debug("Testing invert...");
    UNITTEST_ASSERT(test_id(Create::invert(bv_x)));

    Utils::Log::debug("Testing neg...");
    UNITTEST_ASSERT(test_id(Create::neg<Ex::FP>(fp_x)));
    UNITTEST_ASSERT(test_id(Create::neg<Ex::BV>(bv_x)));

    Utils::Log::debug("Testing reverse...");
    const auto also_x { Create::reverse(Create::reverse(bv_x)) };
    UNITTEST_ASSERT(z3bk.simplify(also_x) == bv_x);


    // UInt Binary

    Utils::Log::debug("Testing signext...");
    UNITTEST_ASSERT(test_id(Create::sign_ext(bv_x, 1)));

    Utils::Log::debug("Testing zeroext...");
    UNITTEST_ASSERT(test_id(Create::zero_ext(bv_x, 1)));


    // Binary

    Utils::Log::debug("Testing eq...");
    UNITTEST_ASSERT(test_id(Create::eq<Ex::FP>(fp_x, fp_y)));
    UNITTEST_ASSERT(test_id(Create::eq<Ex::Bool>(bool_x, bool_y)));
    /* UNITTEST_ASSERT(test_id(Create::eq<Ex::String>(string_x, string_y))); */

    Utils::Log::debug("Testing neq...");
    UNITTEST_ASSERT(test_id(Create::neq<Ex::FP>(fp_x, fp_y)));
    UNITTEST_ASSERT(test_id(Create::neq<Ex::Bool>(bool_x, bool_y)));
    /* UNITTEST_ASSERT(test_id(Create::neq<Ex::String>(string_x, string_y))); */

    using C = Mode::Compare;
    Utils::Log::debug("Testing compare...");
    UNITTEST_ASSERT(test_id(Create::compare<Ex::FP, C::Signed | C::Less | C::Eq>(fp_x, fp_y)));
    UNITTEST_ASSERT(test_id(Create::compare<Ex::FP, C::Signed | C::Less | C::Neq>(fp_x, fp_y)));
    UNITTEST_ASSERT(test_id(Create::compare<Ex::FP, C::Signed | C::Greater | C::Eq>(fp_x, fp_y)));
    UNITTEST_ASSERT(test_id(Create::compare<Ex::FP, C::Signed | C::Greater | C::Neq>(fp_x, fp_y)));

    UNITTEST_ASSERT(test_id(Create::compare<Ex::BV, C::Signed | C::Less | C::Eq>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(Create::compare<Ex::BV, C::Signed | C::Less | C::Neq>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(Create::compare<Ex::BV, C::Signed | C::Greater | C::Eq>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(Create::compare<Ex::BV, C::Signed | C::Greater | C::Neq>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(Create::compare<Ex::BV, C::Unsigned | C::Less | C::Eq>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(Create::compare<Ex::BV, C::Unsigned | C::Less | C::Neq>(bv_x, bv_y)));
    UNITTEST_ASSERT(
        test_id(Create::compare<Ex::BV, C::Unsigned | C::Greater | C::Eq>(bv_x, bv_y)));
    UNITTEST_ASSERT(
        test_id(Create::compare<Ex::BV, C::Unsigned | C::Greater | C::Neq>(bv_x, bv_y)));

    Utils::Log::debug("Testing sub...");
    UNITTEST_ASSERT(test_id(Create::sub(bv_x, bv_y)));

    Utils::Log::debug("Testing div...");
    UNITTEST_ASSERT(test_id(Create::div<true>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(Create::div<false>(bv_x, bv_y)));

    Utils::Log::debug("Testing mod...");
    UNITTEST_ASSERT(test_id(Create::mod<true>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(Create::mod<false>(bv_x, bv_y)));

    using M = Mode::Shift;
    Utils::Log::debug("Testing shift...");
    UNITTEST_ASSERT(test_id(Create::shift<M::Left>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(Create::shift<M::LogicalRight>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(Create::shift<M::ArithmeticRight>(bv_x, bv_y)));

    using LR = Mode::LR;
    Utils::Log::debug("Testing rotate...");
    UNITTEST_ASSERT(test_id(Create::rotate<LR::Left>(bv_x, bv_y)));
    UNITTEST_ASSERT(test_id(Create::rotate<LR::Right>(bv_x, bv_y)));

    Utils::Log::debug("Testing concat...");
    UNITTEST_ASSERT(test_id(Create::concat<Ex::BV>(bv_x, bv_y)));
    /* UNITTEST_ASSERT(test_id(Create::concat<Ex::String>(string_x, string_y))); */

    // Flat

    Utils::Log::debug("Testing add...");
    UNITTEST_ASSERT(test_id(Create::add({ bv_x, bv_y })));

    Utils::Log::debug("Testing mul...");
    UNITTEST_ASSERT(test_id(Create::mul({ bv_x, bv_y })));

    Utils::Log::debug("Testing or...");
    UNITTEST_ASSERT(test_id(Create::or_<Ex::BV>({ bv_x, bv_y })));
    UNITTEST_ASSERT(test_id(Create::or_<Ex::Bool>({ bool_x, bool_y })));

    Utils::Log::debug("Testing and...");
    UNITTEST_ASSERT(test_id(Create::and_<Ex::BV>({ bv_x, bv_y })));
    UNITTEST_ASSERT(test_id(Create::and_<Ex::Bool>({ bool_x, bool_y })));

    Utils::Log::debug("Testing xor...");
    UNITTEST_ASSERT(test_id(Create::xor_({ bv_x, bv_y })));
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(normal)
