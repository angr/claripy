/**
 * @file
 * \ingroup utils
 * @brief This file defines a method to compile-time select a variable
 * Like std::conditional but with values
 */
#ifndef __UTILS_SELECT_HPP__
#define __UTILS_SELECT_HPP__


namespace Utils {

    /** If B return IfTrue, else IfFalse */
    template <bool B, auto IfTrue, auto IfFalse>
    inline const constexpr auto select { B ? IfTrue : IfFalse };

    /** constexpr If B return IfTrue, else IfFalse
     *  To pass things by reference, make InT a reference type
     */
    template <bool B, const InT, const OutT = InT>
    inline constexpr OutT select_constexpr(const InT if_true, const InT if_false) {
        if constexpr (B) {
            return if_true;
        }
        else {
            return if_false;
        }
    }

} // namespace Utils

#endif
