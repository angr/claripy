/**
 * @file
 * \ingroup util
 * @brief This file define type traits for functions
 */
#ifndef R_SRC_UTIL_TYPE_FUNCTION_HPP_
#define R_SRC_UTIL_TYPE_FUNCTION_HPP_

#include <tuple>


namespace Util::Type {

    /** This class is used to get function type traits */
    template <typename...> struct Function;

    /** This class is used to get function type traits
     *  This specialization accepts only function types as input
     */
    template <typename Func, typename... Args> struct Function<Func(Args...)> {

        /** Get the type of the i'th argument of the function type */
        template <std::size_t i> using Arg = std::tuple_element_t<i, std::tuple<Args...>>;
    };

} // namespace Util::Type

#endif
