/**
 * @file
 * \ingroup unittest
 */
#include "create.hpp"
#include "dcast.hpp"
#include "testlib.hpp"


/** Test the literal create function with type T */
template <typename T, typename Data> void literal_t(Data data, const Constants::UInt size = 0) {

    // Test
    const auto lit { Create::literal(Data { data }) };

    // Pointer checks
    UNITTEST_ASSERT(lit.use_count() == 1);
    UNITTEST_ASSERT(lit->op.use_count() == 1);

    // Symbolic check
    UNITTEST_ASSERT(not lit->symbolic);

    // Type check
    const auto op_down { dcast<Op::Literal>(lit->op) };
    const auto exp_down { dcast<T>(lit) };

    // Contains check
    UNITTEST_ASSERT(std::get<Data>(op_down->value) == data);

    // Size check
    if constexpr (Utils::is_ancestor<Expression::Bits, T>) {
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
    literal_t<Expression::String>(data_s, C_CHAR_BIT * data_s.size());
    literal_t<Expression::BV>(data_v, C_CHAR_BIT * data_v.size());
    literal_t<Expression::FP>(3.4, 64_ui);  // NOLINT
    literal_t<Expression::FP>(3.4f, 32_ui); // NOLINT
    auto ptr { std::make_shared<const PyObj::VS>(1, 1, C_CHAR_BIT) };
	const auto bl { ptr->bit_length };
    literal_t<Expression::VS>(std::move(ptr), bl);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(literal)
