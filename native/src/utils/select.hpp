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

} // namespace Utils

#endif
