/**
 * @file
 * \ingroup util
 * @brief This file defines a method for determining if T is in a type list Args...
 */
#ifndef R_SRC_UTIL_TYPE_IS_IN_HPP_
#define R_SRC_UTIL_TYPE_IS_IN_HPP_

#include "ancestor.hpp"
#include "same.hpp"

#include "../list.hpp"


namespace Util::Type::Is {

    /** Return true if T in Args */
    template <typename T, typename... Args> UTIL_ICCBOOL in { List<Args...>::template contains<T> };

    /** Return true if T in Args; ignores const-ness of everything */
    template <typename T, typename... Args>
    UTIL_ICCBOOL in_ignore_const { (same_ignore_const<T, Args> || ...) };

    /** Return true if Is::ancestor<Args[i], T> for any i */
    template <typename T, typename... Args> UTIL_ICCBOOL ancestor_in { (ancestor<Args, T> || ...) };

} // namespace Util::Type::Is

#endif
