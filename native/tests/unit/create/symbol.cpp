/**
 * @file
 * \ingroup unittest
 */
#include "dcast.hpp"

#include <testlib/testlib.hpp>


/** Test the symbol create function with type T */
template <typename T> void symbol_t() {
    static int n_runs = 0;

    // Create name
    std::string name { std::to_string(++n_runs) };
    const std::string name_copy { name };
    const U64 size { 0x10 };

    // Test
    Expr::BasePtr sym;
    if constexpr (Util::Type::Is::ancestor<Expr::Bits, T>) {
        sym = Create::symbol<T>(std::move(name), size, { nullptr });
    }
    else {
        sym = Create::symbol_bool(std::move(name));
    }

    // Pointer checks
    UNITTEST_ASSERT(sym.use_count() == 1);
    UNITTEST_ASSERT(sym->op.use_count() == 1);

    // Symbolic check
    UNITTEST_ASSERT(sym->symbolic);

    // Type check
    const auto op_down { dcast<Op::Symbol>(sym->op) };
    const auto exp_down { dcast<T>(sym) };

    // Contains check
    UNITTEST_ASSERT(op_down->name == name_copy);

    // Size check
    if constexpr (Util::Type::Is::ancestor<Expr::Bits, T>) {
        UNITTEST_ASSERT(exp_down->bit_length == size);
    }

    // For compilation
    (void) size;
}

/** Test the symbol create function */
void symbol() {
    symbol_t<Expr::Bool>();
    symbol_t<Expr::String>();
    symbol_t<Expr::BV>();
    symbol_t<Expr::VS>();
    symbol_t<Expr::FP>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(symbol)
