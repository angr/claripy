/**
 * @file
 * \ingroup util
 * @brief This file contains declares the Util:inc() function
 */
#ifndef R_SRC_UTIL_INC_HPP_
#define R_SRC_UTIL_INC_HPP_

#include "type.hpp"

#include "../constants.hpp"

#include <atomic>


#define M_ATOM_T std::atomic<U64>
namespace Util {

    /** Thread-safe-ly increment a static number and return the result
     *  The template Args are used as a map key to allow this function to be reused as needed
     *  This function is primarily meant to run before main to help configure things
     */
    template <typename... Args, std::enable_if_t<Type::Has::pre_inc_op<M_ATOM_T>, int> = 0>
    inline U64 inc() noexcept {
        // If an exception is thrown, we *should* crash
        static M_ATOM_T ret(0);
        return ++ret;
    }

} // namespace Util

#undef M_ATOM_T

#endif
