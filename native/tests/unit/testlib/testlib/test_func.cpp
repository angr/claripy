/**
 * @file
 * \ingroup testlib
 */
#include "test_func.hpp"

#include "error.hpp"
#include "private/verify.hpp"
#include "utils.hpp"

#include <exception>


/** Catch and print an error before exiting */
#define CATCH_ERROR(ERROR)                                                                        \
    catch (const ERROR &e) {                                                                      \
        UNITTEST_ERR(#ERROR, ": ", e.what())                                                      \
    }


int UnitTest::TestLib::test_func(TestFN &f) {
    // Notify verify that test_func has started running
    Private::verify();
    // Test f
    try {
        f();
        return EXIT_SUCCESS;
    }
    // UnitTest error
    catch (Error &e) {
        Utils::Log::error(e.what());
        return EXIT_FAILURE;
    }
    // If there was an different error, note so and fail
    CATCH_ERROR(Utils::Error::Unexpected::Base)
    CATCH_ERROR(Utils::Error::Python::Base)
    CATCH_ERROR(Utils::Error::Claricpp)
    CATCH_ERROR(std::exception)
}
