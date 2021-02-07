/**
 * @file
 * \ingroup utils
 * @brief This file defines a method to determine if Derived derives from or is Base
 */
#ifndef __UTILS_ISANCESTOR_HPP__
#define __UTILS_ISANCESTOR_HPP__

#include "is_same.hpp"
#include "transfer_const.hpp"

#include <type_traits>


namespace Utils {

    /** Return true if Derived is Base or subclasses Base
     *  Unlike is_base_of, this returns true for <T, T> where T is a primitive
     */
    template <typename Base, typename Derived>
    UTILS_ICCBOOL is_ancestor { is_exactly_same<TransferConst<Base, Derived>, Derived> ||
                                std::is_base_of_v<Base, Derived> };

} // namespace Utils

#endif
