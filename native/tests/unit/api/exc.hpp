/**
 * @file
 * @brief Defines helpers for API tests
 * \ingroup unittest
 */
#ifndef R_UNIT_API_EXC_HPP_
#define R_UNIT_API_EXC_HPP_

#include "testlib.hpp"


/** A function which unittest verifies an API call did not raise an exception */
inline void exc() {
    if (!claricpp_has_exception()) {
        return;
    }
    const auto e { claricpp_get_exception() };
    std::stringstream s;
    s << "Claricpp API rose the following exception:\nType: " << e.type << "\nMsg: " << e.msg
      << "\nTrace: " << e.trace;
    UNITTEST_ERR(s.str());
}

/** A function which returns its input but calls exc */
template <typename T> inline T exc(const T in) {
    exc();
    return in;
}

#endif
