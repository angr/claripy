/**
 * @file
 * \ingroup utils
 * @brief This file defines Utils::type_pun
 */
#ifndef __UTILS_TYPEPUN_HPP__
#define __UTILS_TYPEPUN_HPP__

#include "../constants.hpp"

#include <cstring>


namespace Utils {

    /** This is a safe way to type pun in C++
     *  Unions can have undefined behavior when type punning
     *  Because of C++'s 'strict anti-aliasing' rules, type punning via casting
     *  can have undefined behavior, especially with -O2 or higher level optimizations
     */
    template <typename Out> inline Out type_pun(Constants::CCSC in) {
        Out ret;
        std::memcpy(&ret, in, sizeof(Out));
        return ret;
    }

} // namespace Utils

#endif
