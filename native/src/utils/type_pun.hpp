/**
 * @file
 * \ingroup utils
 * @brief This file defines Utils::type_pun
 */
#ifndef __UTILS_TYPEPUN_HPP__
#define __UTILS_TYPEPUN_HPP__

#include "dependent_constant.hpp"

#include "../constants.hpp"

#include <cstring>


namespace Utils {

    /** This is a safe way to type pun in C++ provided that the Out type is
     *  well formed no matter what arrangement of bits its representation has
     *  For example, ints are safe, doubles are not since they have some undefined forms
     *  Unions can have undefined behavior when type punning
     *  Because of C++'s 'strict anti-aliasing' rules, type punning via casting
     *  can have undefined behavior, especially with -O2 or higher level optimizations
     *  Warning: If Array is true, it is the programmer's job to ensure in is large enough to
     *  pun to an Out! Array is simply a default safety check
     */
    template <typename Out, typename In, bool InIsArray = false>
    inline Out type_pun(Constants::CTSC<In> in) {
        // Error checking
        if constexpr (!InIsArray) {
            // The actual error condition
            static_assert((sizeof(Out) <= sizeof(In)) && TD::true_<Out, In>,
                          "type_pun will not pun to a size larger than its input");
        }
        // Type pun
        Out ret;
        // Not memmove since compilers seem to be more capable of no-op-ing memcpy with -O3
        std::memcpy(&ret, in, sizeof(Out));
        return ret;
    }

} // namespace Utils

#endif
