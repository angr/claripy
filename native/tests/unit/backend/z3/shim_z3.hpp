/**
 * @file
 * @brief A shim of the z3 backend which exposes private members
 * \ingroup unittest
 */
#ifndef R_TESTS_UNIT_BACKEND_Z3_SHIMZ3_HPP_
#define R_TESTS_UNIT_BACKEND_Z3_SHIMZ3_HPP_

#include <testlib/testlib.hpp>


struct UnitTest::Friend {
    /** A Shim of the Z3 backend which exposes private variables */
    struct ShimZ3 {
        /** The Z3 backend */
        Backend::Z3::Z3 bk {};
        /** Z3.convert */
        template <typename T> auto convert(const T b) { return bk.convert(b); }
        /** Z3.abstract */
        template <typename T> auto abstract(const T &b) { return bk.abstract(b); }
    };
};

#endif
