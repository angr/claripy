/**
 * @file
 * \ingroup testlib
 * @brief This defines a UnitTest error and wrapping macros
 */
#ifndef __TESTS_UNIT_TESTLIB_TESTLIB_ERROR_HPP__
#define __TESTS_UNIT_TESTLIB_TESTLIB_ERROR_HPP__

#include "utils.hpp"


/** A unittest assertion macro */
#define UNITTEST_ASSERT(B)                                                                        \
    if (!(B)) {                                                                                   \
        throw UnitTest::TestLib::Error("");                                                       \
    }

/** A unittest assertion macro */
#define UNITTEST_ASSERT_MSG(B, ...)                                                               \
    if (!(B)) {                                                                                   \
        throw UnitTest::TestLib::Error(__VA_ARGS__);                                              \
    }

namespace UnitTest::TestLib {

    /** The UnitTest error struct */
    DEFINE_NAMESPACED_SUBCLASS_WITH_CONSTRUCTOR(Error, Claricpp, Utils::Error)

} // namespace UnitTest::TestLib

#endif
