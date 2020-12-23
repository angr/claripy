/**
 * @file
 * @brief Forward declares things related to unit testing
 */
#ifndef __UNITTEST_HPP__
#define __UNITTEST_HPP__

/** Allows the friend access for unittests */
#define ENABLE_UNITTEST_FRIEND_ACCESS                                                             \
    /** Allows the friend access for unittests */                                                 \
    friend struct Tests::Native::ClaricppUnitTest;


/** A namespace used for tests */
namespace Tests {

    /** A namespace used for native tests */
    namespace Native {

        /** A struct used to give friend access to unittests */
        struct ClaricppUnitTest;

    } // namespace Native

} // namespace Tests

#endif
