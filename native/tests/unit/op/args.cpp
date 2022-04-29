/**
 * @file
 * \ingroup unittest
 */
#include <algorithm>
#include <testlib/testlib.hpp>


/** Verify the two arg getter functions of o do not contradict */
static void test_op(const Op::BasePtr &op) {
    Op::Stack stack;
    Util::Log::debug("Testing op: ", op->op_name());

    // Call functions
    Op::unsafe_add_reversed_children(*op, stack);
    const std::vector<Op::ArgVar> args { op->python_children() };

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

    // Constants
    const auto ntz { Mode::FP::Rounding::NearestTiesEven };
    const auto true_ { C::literal(true) };
    const auto str_sym { C::symbol_string("str_sym", 64) };
    const auto bv_sym { C::symbol_bv("bv_sym", 64) };
    const auto fp_sym { C::symbol_fp("fp_sym", 64) };

    // Functions
    const auto u64 { [](const U64 i) { return C::literal(i); } };
    const auto test { [](Expr::BasePtr e) { return test_op(e->op); } }; // NOLINT (copy is ok)

    // Non-trivial
    test(u64(4));
    test(bv_sym);
    test(C::if_(true_, u64(4), bv_sym));
    test(C::extract(1, 0, bv_sym));

    // FP
    test(C::FP::from_2s_complement_bv_signed(ntz, bv_sym, Mode::FP::dbl));
    test(C::FP::from_2s_complement_bv_unsigned(ntz, bv_sym, Mode::FP::dbl));
    test(C::FP::from_not_2s_complement_bv(bv_sym, Mode::FP::dbl));
    test(C::FP::from_fp(ntz, fp_sym, Mode::FP::dbl));
    test(C::FP::to_bv_signed(ntz, fp_sym, 64));
    test(C::FP::to_bv_unsigned(ntz, fp_sym, 64));

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

    // U64 Binary
    test(C::sign_ext(bv_sym, 1));
    test(C::zero_ext(bv_sym, 1));

    // Binary

    // Compare
    test(C::eq(bv_sym, bv_sym));
    test(C::neq(bv_sym, bv_sym));
    test(C::ugt(bv_sym, bv_sym));
    test(C::uge(bv_sym, bv_sym));
    test(C::ult(bv_sym, bv_sym));
    test(C::ule(bv_sym, bv_sym));
    test(C::sgt(bv_sym, bv_sym));
    test(C::sge(bv_sym, bv_sym));
    test(C::slt(bv_sym, bv_sym));
    test(C::sle(bv_sym, bv_sym));

    // Math
    test(C::sub(bv_sym, bv_sym));
    test(C::div_signed(bv_sym, bv_sym));
    test(C::div_unsigned(bv_sym, bv_sym));
    test(C::mod_signed(bv_sym, bv_sym));
    test(C::mod_unsigned(bv_sym, bv_sym));

    // Bitwise
    test(C::shift_l(bv_sym, bv_sym));
    test(C::shift_logical_right(bv_sym, bv_sym));
    test(C::shift_arithmetic_right(bv_sym, bv_sym));
    test(C::rotate_right(bv_sym, bv_sym));
    test(C::rotate_left(bv_sym, bv_sym));

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
