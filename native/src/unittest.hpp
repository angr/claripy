/**
 * @file
 * @brief Forward declares things related to unit testing
 */
#ifndef R_SRC_UNITTEST_HPP_
#define R_SRC_UNITTEST_HPP_

#ifndef ENABLE_TESTING
    #define ENABLE_UNITTEST_FRIEND_ACCESS
#else

    /** Allows the friend access for unittests */
    #define ENABLE_UNITTEST_FRIEND_ACCESS                                                          \
        /** Allows the friend access for unittests */                                              \
        friend struct UnitTest::Friend;

namespace UnitTest {

    /** A struct used to give friend access to unittests */
    struct [[maybe_unused]] Friend;

} // namespace UnitTest

#endif

#endif
