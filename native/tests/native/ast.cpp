#define BOOST_TEST_MODULE ast
#include <boost/test/included/unit_test.hpp>

/** For brevity */
namespace UT = boost::unit_test;


/** Create test2, which depends on s1's test1 */
BOOST_AUTO_TEST_CASE(test2, *UT::depends_on("s1/test1")) {
    // Assert true
    BOOST_TEST(true);
}

/** Create a test suite called s1 */
BOOST_AUTO_TEST_SUITE(s1)

/** Declare a test suite test case, name it test1 */
BOOST_AUTO_TEST_CASE(test1) {
    // Assert true
    BOOST_TEST(true);
}

// End test suite
BOOST_AUTO_TEST_SUITE_END()
