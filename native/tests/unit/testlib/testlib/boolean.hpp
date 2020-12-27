/**
 * @file
 * @brief This defins the boolean function
 */
#ifndef __TESTS_UNIT_TESTLIB_BOOLEAN_HPP__
#define __TESTS_UNIT_TESTLIB_BOOLEAN_HPP__

namespace UnitTest {

    /** Convert T into a boolean */
    template <typename T> bool boolean(T t) {
        if (t) {
            return true;
        }
        else {
            return false;
        }
    }

} // namespace UnitTest


#endif
