/**
 * @file
 * \ingroup unittest
 */
#include "create.hpp"
#include "testlib.hpp"


/** Verify that the symbol function compiles and can be run without issue */
void symbol() {

    // Non-Bits subclass test
    (void) Create::symbol<Expression::Bool>(Create::EAnVec {}, "mysym");

    // Bits subclass test
    (void) Create::symbol<Expression::BV>(Create::EAnVec {}, "mysym2", 10);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(symbol)
