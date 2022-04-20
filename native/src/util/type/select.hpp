/**
 * @file
 * \ingroup util
 * @brief This file defines a method to compile-time select a variable
 * Like std::conditional but with values
 */
#ifndef R_SRC_UTIL_TYPE_SELECT_HPP_
#define R_SRC_UTIL_TYPE_SELECT_HPP_


namespace Util::Type {

    /** If B return IfTrue, else IfFalse */
    template <bool B, auto IfTrue, auto IfFalse>
    inline const constexpr auto select { B ? IfTrue : IfFalse };

} // namespace Util::Type

#endif
