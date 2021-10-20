/**
 * @file
 * \ingroup util
 * @brief This file defines a method to determine if Derived derives from or is Base
 */
#ifndef R_UTIL_ISANCESTOR_HPP_
#define R_UTIL_ISANCESTOR_HPP_

#include "is_same.hpp"
#include "transfer_const.hpp"

#include <type_traits>


namespace Util {

    /** Return true if Derived is Base or subclasses Base
     *  Unlike is_base_of, this returns true for <T, T> where T is a primitive
     */
    template <typename Base, typename Derived>
    UTILS_ICCBOOL is_ancestor { is_exactly_same<TransferConst<Base, Derived>, Derived> ||
                                std::is_base_of_v<Base, Derived> };

} // namespace Util

#endif
