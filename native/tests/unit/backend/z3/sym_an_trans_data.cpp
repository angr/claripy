/**
 * @file
 * \ingroup unittest
 */
#include "shim_z3.hpp"

#include <testlib/testlib.hpp>


/** A built-in annotation */
class TestAnnotation final : public Annotation::Base {
    FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(Base)
  public:
    /** Constructor */
    explicit inline TestAnnotation(const Hash::Hash &h, std::string &&s) noexcept
        : Base { h, static_cuid }, str { std::move(s) } {}

    /** Returns whether this annotation can be eliminated in a simplification. */
    [[nodiscard]] inline bool eliminatable() const final { return false; }

    /** Returns whether this annotation can be relocated in a simplification. */
    [[nodiscard]] inline bool relocatable() const final { return false; }

    /** Some data */
    const std::string str; // NOLINT
};

/** Test how the z3 backend handles sym_an_trans_data */
void sym_an_trans_data() {
    UnitTest::Friend::ShimZ3 z3;
    namespace A = Annotation;

    // Create an annotation
    const auto an { A::factory<TestAnnotation>(std::string { "Hello" }) };

    // Create an BV symbol
    const auto an_vec { std::make_shared<A::Vec>(A::Vec::RawVec { an }) };
    const auto sym { Create::symbol<Expr::BV>(std::string { "x" }, 32, an_vec) };

    // Round trip it through z3
    const auto conv { z3.convert(sym.get()) };
    const auto abs { z3.abstract(conv) };

    // Tests
    UNITTEST_ASSERT(sym == abs);
    UNITTEST_ASSERT(sym->annotations == abs->annotations);
    const auto bptr { abs->annotations->vec[0] };
    UNITTEST_ASSERT(sym->annotations->vec[0] == bptr);
    const auto *const cast { dynamic_cast<const TestAnnotation *>(bptr.get()) };
    UNITTEST_ASSERT(cast);
    UNITTEST_ASSERT(cast->str == "Hello");

    // Verify data can be cleared
    z3.bk.clear_persistent_data();
    const auto abs2 { z3.abstract(conv) };
    UNITTEST_ASSERT(sym != abs2);
    UNITTEST_ASSERT(abs != abs2);
    UNITTEST_ASSERT(abs2->annotations == nullptr);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(sym_an_trans_data)
