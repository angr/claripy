/**
 * @file
 * \ingroup testlib
 * @brief This defines a UnitTest error and wrapping macros
 */
#ifndef R_UNIT_TESTLIB_TESTLIB_ERROR_HPP_
#define R_UNIT_TESTLIB_TESTLIB_ERROR_HPP_

#include "utils.hpp"


/** A unittest macro used to throw an error */
#define UNITTEST_ERR(...) throw UnitTest::TestLib::Error(__VA_ARGS__);

/** A unittest assertion macro */
#define UNITTEST_ASSERT(B)                                                                        \
    if (!(B)) {                                                                                   \
        throw UnitTest::TestLib::Error(WHOAMI_WITH_SOURCE "UnitTest Assertion failed.");          \
    }

/** A unittest assertion macro */
#define UNITTEST_ASSERT_MSG(B, ...)                                                               \
    if (!(B)) {                                                                                   \
        throw UnitTest::TestLib::Error(WHOAMI_WITH_SOURCE                                         \
                                       "UnitTest Assertion failed." __VA_ARGS__);                 \
    }

namespace UnitTest::TestLib {

    /** The UnitTest error struct */
    DEFINE_NAMESPACED_FINAL_EXCEPTION(Error, Claricpp, Utils::Error)

} // namespace UnitTest::TestLib

#endif
