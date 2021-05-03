/**
 * @file
 * \ingroup unittest
 */
#include "create.hpp"
#include "dcast.hpp"
#include "testlib.hpp"


/** Test the literal create function with type T */
template <typename T, typename U> void literal_t(U data, const Constants::UInt size = 0) {

    // For brevity
    namespace Ex = Expression; // NOLINT (false positive)

    // Create inputs
    const auto data_copy { data };

    // Test
    Expression::BasePtr lit;
    if constexpr (Utils::is_ancestor<Ex::Bits, T>) {
        lit = Create::literal<T>(Create::EAnVec {}, std::move(data), size);
    }
    else {
        lit = Create::literal<T>(Create::EAnVec {}, std::move(data));
    }

    // Pointer checks
    UNITTEST_ASSERT(lit.use_count() == 1);
    UNITTEST_ASSERT(lit->op.use_count() == 1);

    // Symbolic check
    UNITTEST_ASSERT(not lit->symbolic);

    // Type check
    const auto op_down { dcast<Op::Literal>(lit->op) };
    const auto exp_down { dcast<T>(lit) };

    // Contains check
    UNITTEST_ASSERT(std::get<U>(op_down->value) == data_copy);

    // Size check
    if constexpr (Utils::is_ancestor<Ex::Bits, T>) {
        UNITTEST_ASSERT(exp_down->bit_length == size)
    }

    // For compilation
    (void) size;
}

/** Test the literal create function */
void literal() {

    // Test varaibles
    char data[] = "This is a test"; // NOLINT
    std::string data_s { data };
    std::vector<char> data_v;
    data_v.assign(std::begin(data), std::end(data));

    // Tests
    literal_t<Expression::Bool>(true);
    literal_t<Expression::String>(data_s, data_s.size());
    literal_t<Expression::BV>(data_v, data_v.size());
    literal_t<Expression::FP>(3.4, 64_ui); // NOLINT

#warning Not testing Literal VS
    /* literal_t<Expression::VS>(); */
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(literal)
