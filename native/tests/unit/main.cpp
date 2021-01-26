#include "testlib.hpp"
#include "utils.hpp"

#include <exception>
#include <iostream>


// For brevity
using namespace UnitTest::TestLib;


/** Catch and print an error before exiting */
#define CATCH_ERROR(ERROR)                                                                        \
    catch (const ERROR &e) {                                                                      \
        std::cout << #ERROR << ": " << e.what() << std::endl;                                     \
        return -1;                                                                                \
    }


/** main */
int main() {
    try {
        UNITTEST_ASSERT_MSG(test_func, "Test function may not be nullptr")
        test_func();
        return 0;
    }
    CATCH_ERROR(UnitTest::TestLib::Error)
    CATCH_ERROR(Utils::Error::Unexpected::Base)
    CATCH_ERROR(Utils::Error::Python::Base)
    CATCH_ERROR(Utils::Error::Claricpp)
    CATCH_ERROR(std::exception)
}
