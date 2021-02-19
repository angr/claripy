/**
 * @file
 * \ingroup unittest
 */
#include "../binary.hpp"
#include "../unary.hpp"


/** Test the trivial create functions */
void trivial() {
    namespace Log = Utils::Log;
    namespace Ex = Expression;
    namespace Cr = Create;

    /********************************************************************/
    /*                              Unary                               */
    /********************************************************************/

    Log::debug("Testing String::is_digit...");
    unary<Ex::Bool, Ex::String, Op::String::IsDigit, Cr::String::is_digit>();

    /********************************************************************/
    /*                            Int Binary                            */
    /********************************************************************/

    Log::debug("Testing to_int...");
    int_binary<Ex::BV, Op::ToInt, SM::Second, Cr::String::to_int>();

    /********************************************************************/
    /*                              Binary                              */
    /********************************************************************/

    Log::debug("Testing String::contains...");
    binary<Ex::Bool, Ex::String, Op::String::Contains, SM::NA, Cr::String::contains>();

    Log::debug("Testing String::prefix_of...");
    binary<Ex::Bool, Ex::String, Op::String::PrefixOf, SM::NA, Cr::String::prefix_of>();

    Log::debug("Testing String::suffix_of...");
    binary<Ex::Bool, Ex::String, Op::String::SuffixOf, SM::NA, Cr::String::suffix_of>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(trivial)
