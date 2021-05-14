/**
 * @file
 * \ingroup utils
 * @brief This file defines a method to compile-time select a variable
 * Like std::conditional but with values
 */
#ifndef R_UTILS_SELECT_HPP_
#define R_UTILS_SELECT_HPP_


namespace Utils {

    /** If B return IfTrue, else IfFalse */
    template <bool B, auto IfTrue, auto IfFalse>
    inline const constexpr auto select { B ? IfTrue : IfFalse };

} // namespace Utils

#endif
