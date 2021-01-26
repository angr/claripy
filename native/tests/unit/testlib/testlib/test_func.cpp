/**
 * @file
 * \ingroup testlib
 */
#include "test_func.hpp"

#include "error.hpp"
#include "utils.hpp"

#include <exception>


/** Catch and print an error before exiting */
#define CATCH_ERROR(ERROR)                                                                        \
    catch (const ERROR &e) {                                                                      \
        UNITTEST_ERR(#ERROR, ": ", e.what())                                                      \
    }


void UnitTest::TestLib::test_func(TestFN &f) {
    try {
        f();
        return;
    }
    CATCH_ERROR(UnitTest::TestLib::Error)
    CATCH_ERROR(Utils::Error::Unexpected::Base)
    CATCH_ERROR(Utils::Error::Python::Base)
    CATCH_ERROR(Utils::Error::Claricpp)
    CATCH_ERROR(std::exception)
}
