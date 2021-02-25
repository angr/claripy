/**
 * @file
 * \ingroup unittest
 */
#include "create.hpp"
#include "dcast.hpp"
#include "testlib.hpp"


/** Test the literal create function with type T */
template <typename T> void literal_t() {

    // For brevity
    namespace Ex = Expression; // NOLINT (false positive)

    // Create inputs
    std::string data { "This is data!" };
    const std::string data_copy { data };
    const auto size { BitLength::char_bit * data.size() };

    // Test
    Expression::BasePtr lit;
    if constexpr (Utils::is_ancestor<Ex::Bits, T>) {
        lit = Create::literal<T>(Create::EAnVec {}, std::move(data), size);
    }
    else {
        lit = Create::literal<T>(Create::EAnVec {}, std::move(data));
    }

    // Pointer checks
    UNITTEST_ASSERT(lit.use_count() == 1)
    UNITTEST_ASSERT(lit->op.use_count() == 1)

    // Symbolic check
    UNITTEST_ASSERT(not lit->symbolic)

    // Type check
    const auto op_down { dcast<Op::Literal>(lit->op) };
    const auto exp_down { dcast<T>(lit) };

    // Contains check
    UNITTEST_ASSERT(op_down->value == data_copy)

    // Size check
    if constexpr (Utils::is_ancestor<Ex::Bits, T>) {
        UNITTEST_ASSERT(exp_down->bit_length == size)
    }

    // For compilation
    (void) size;
}

/** Test the literal create function */
void literal() {
    literal_t<Expression::Bool>();
    literal_t<Expression::String>();
    literal_t<Expression::BV>();
    literal_t<Expression::VS>();
    literal_t<Expression::FP>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(literal)
