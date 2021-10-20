/**
 * @file
 * \ingroup testlib
 */
#include "test_func.hpp"

#include "error.hpp"
#include "private/verify.hpp"
#include "util.hpp"

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
        Util::Log::error(e.what());
        return EXIT_FAILURE;
    }
    // If there was a different error, note so and fail
    CATCH_ERROR(Util::Error::Unexpected)
    CATCH_ERROR(Util::Error::Python::Base)
    CATCH_ERROR(Util::Error::Claricpp)
    CATCH_ERROR(std::exception)
}
