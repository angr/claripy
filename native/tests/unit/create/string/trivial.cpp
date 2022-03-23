/**
 * @file
 * \ingroup unittest
 */
#include "../binary.hpp"
#include "../uint_binary.hpp"
#include "../unary.hpp"


/** Test the trivial create functions */
void trivial() {
    namespace Log = Util::Log;
    namespace Cr = Create;

    /********************************************************************/
    /*                              Unary                               */
    /********************************************************************/

    Log::debug("Testing String::is_digit...");
    unary<Expr::Bool, Expr::String, Op::String::IsDigit, Cr::String::is_digit>();

    /********************************************************************/
    /*                            I64 Binary                            */
    /********************************************************************/

    Log::debug("Testing to_int...");
    uint_binary<Expr::BV, Expr::String, Op::String::ToInt, SM::Second, Cr::String::to_int>();

    Log::debug("Testing str_len...");
    uint_binary<Expr::BV, Expr::String, Op::String::Len, SM::Second, Cr::String::len>();

    /********************************************************************/
    /*                              Binary                              */
    /********************************************************************/

    Log::debug("Testing String::contains...");
    binary<Expr::Bool, Expr::String, Op::String::Contains, SM::NA, Cr::String::contains>();

    Log::debug("Testing String::prefix_of...");
    binary<Expr::Bool, Expr::String, Op::String::PrefixOf, SM::NA, Cr::String::prefix_of>();

    Log::debug("Testing String::suffix_of...");
    binary<Expr::Bool, Expr::String, Op::String::SuffixOf, SM::NA, Cr::String::suffix_of>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(trivial)
