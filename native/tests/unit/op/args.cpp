/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"

#include <algorithm>


/** Verify the two arg getter functions of o do not contradict */
static void test_op(const Op::BasePtr &op) {
    Op::Stack stack;
    std::vector<Op::ArgVar> args;
    Util::Log::debug("Testing op: ", op->op_name());

    // Call functions
    op->unsafe_add_reversed_children(stack);
    op->python_children(args);

    // Filter args
    std::vector<Expr::RawPtr> filtered {};
    for (const auto &i : args) {
        try {
            filtered.emplace_back(std::get<Expr::BasePtr>(i).get());
        }
        catch (std::bad_variant_access &) {
        }
    }

    // Compare
    UNITTEST_ASSERT(stack.size() == filtered.size());
    for (const auto &i : filtered) {
        const auto &top { stack.top() };
        UNITTEST_ASSERT(top == i);
        stack.pop();
    }
    Util::Log::verbose("Success");
}

/** Verify that the two arg getter functions do not contradict each other */
void args() {
    namespace C = Create;
    using Cmp = Mode::Compare;

    // Constants
    const auto ntz { Mode::FP::Rounding::NearestTiesEven };
    const auto true_ { C::literal(true) };
    const auto str_sym { C::symbol<Expr::String>("str_sym", 64) };
    const auto bv_sym { C::symbol<Expr::BV>("bv_sym", 64) };
    const auto fp_sym { C::symbol<Expr::FP>("fp_sym", 64) };

    // Functions
    const auto u64 { [](const UInt i) { return C::literal(i); } };
    const auto test { [](Expr::BasePtr e) { return test_op(e->op); } }; // NOLINT (copy is ok)

    // Non-trivial
    test(u64(4));
    test(bv_sym);
    test(C::if_(true_, u64(4), bv_sym));
    test(C::extract(1, 0, bv_sym));

    // FP
    test(C::FP::from_2s_complement_bv<true>(ntz, bv_sym, Mode::FP::dbl));
    test(C::FP::from_2s_complement_bv<false>(ntz, bv_sym, Mode::FP::dbl));
    test(C::FP::from_not_2s_complement_bv(bv_sym, Mode::FP::dbl));
    test(C::FP::from_fp(ntz, fp_sym, Mode::FP::dbl));
    test(C::FP::to_bv<true>(ntz, fp_sym, 64));
    test(C::FP::to_bv<false>(ntz, fp_sym, 64));

    // String
    test(C::String::from_int(bv_sym));
    test(C::String::index_of(str_sym, str_sym, bv_sym, 64));
    test(C::String::replace(str_sym, str_sym, str_sym));
    test(C::String::sub_string(bv_sym, bv_sym, str_sym));

    /********************************************************************/
    /*                             Trivial                              */
    /********************************************************************/

    // Unary
    test(C::abs(fp_sym));
    test(C::neg(bv_sym));
    test(C::not_(true_));
    test(C::invert(bv_sym));
    test(C::reverse(bv_sym));

    // UInt Binary
    test(C::sign_ext(bv_sym, 1));
    test(C::zero_ext(bv_sym, 1));

    // Binary

    // Compare
    test(C::eq(bv_sym, bv_sym));
    test(C::neq(bv_sym, bv_sym));
    test(C::compare<Cmp::Unsigned | Cmp::Greater | Cmp::Neq>(bv_sym, bv_sym));
    test(C::compare<Cmp::Unsigned | Cmp::Greater | Cmp::Eq>(bv_sym, bv_sym));
    test(C::compare<Cmp::Unsigned | Cmp::Less | Cmp::Neq>(bv_sym, bv_sym));
    test(C::compare<Cmp::Unsigned | Cmp::Less | Cmp::Eq>(bv_sym, bv_sym));
    test(C::compare<Cmp::Signed | Cmp::Greater | Cmp::Neq>(bv_sym, bv_sym));
    test(C::compare<Cmp::Signed | Cmp::Greater | Cmp::Eq>(bv_sym, bv_sym));
    test(C::compare<Cmp::Signed | Cmp::Less | Cmp::Neq>(bv_sym, bv_sym));
    test(C::compare<Cmp::Signed | Cmp::Less | Cmp::Eq>(bv_sym, bv_sym));

    // Math
    test(C::sub(bv_sym, bv_sym));
    test(C::div<true>(bv_sym, bv_sym));
    test(C::div<false>(bv_sym, bv_sym));
    test(C::mod<true>(bv_sym, bv_sym));
    test(C::mod<false>(bv_sym, bv_sym));

    // Bitwise
    test(C::shift<Mode::Shift::Left>(bv_sym, bv_sym));
    test(C::shift<Mode::Shift::LogicalRight>(bv_sym, bv_sym));
    test(C::shift<Mode::Shift::ArithmeticRight>(bv_sym, bv_sym));
    test(C::rotate<Mode::LR::Right>(bv_sym, bv_sym));
    test(C::rotate<Mode::LR::Left>(bv_sym, bv_sym));

    // Misc
    test(C::widen(bv_sym, bv_sym));
    test(C::union_(bv_sym, bv_sym));
    test(C::intersection_(bv_sym, bv_sym));
    test(C::concat(bv_sym, bv_sym));

    // Flat
    test(C::add({ bv_sym, bv_sym }));
    test(C::mul({ bv_sym, bv_sym }));
    test(C::or_({ bv_sym, bv_sym }));
    test(C::and_({ bv_sym, bv_sym }));
    test(C::xor_({ bv_sym, bv_sym }));

    /********************************************************************/
    /*                           FP Trivial                             */
    /********************************************************************/

    test(C::FP::to_ieee_bv(fp_sym));
    test(C::FP::add(fp_sym, fp_sym, ntz));
    test(C::FP::sub(fp_sym, fp_sym, ntz));
    test(C::FP::mul(fp_sym, fp_sym, ntz));
    test(C::FP::div(fp_sym, fp_sym, ntz));
    test(C::FP::fp(bv_sym, bv_sym, bv_sym));

    /********************************************************************/
    /*                          String Trivial                          */
    /********************************************************************/

    test(C::String::is_digit(str_sym));
    test(C::String::to_int(str_sym, 64));
    test(C::String::len(str_sym, 64));
    test(C::String::contains(str_sym, str_sym));
    test(C::String::prefix_of(str_sym, str_sym));
    test(C::String::suffix_of(str_sym, str_sym));
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(args)
