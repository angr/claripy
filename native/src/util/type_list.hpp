#ifndef R_UTIL_TYPELIST_HPP_
#define R_UTIL_TYPELIST_HPP_

#include "macros.hpp"
#include "unconstructable.hpp"

#include "../constants.hpp"


namespace Util {

    /** An uninstantiable type list class */
    template <typename... Args> struct TypeList : public Unconstructable {
        struct Private; // Forward declare

        // Conversions

        /** Return a Container<Args..., Other...> */
        template <template <typename...> typename Container, typename... Other>
        using ApplyWith = Container<Args..., Other...>;

        /** Return a Container<Args...> */
        template <template <typename...> typename Container> using Apply = Container<Args...>;

        /** Returns the length of the typelist */
        static inline constexpr const UInt len { sizeof...(Args) };

        // TypeList generators

        /** Return TypeList<Other..., Args...> */
        template <typename... Other> using Prepend = TypeList<Other..., Args...>;

        /** Return TypeList<Args..., Other...> */
        template <typename... Other> using Append = TypeList<Args..., Other...>;

        /** Return true if T in Args */
        template <typename T> static UTIL_ICCBOOL contains { (std::is_same_v<T, Args> || ...) };

        /** Return a TypeList containing Args... set minus the types in the type list TL */
        template <typename TL> using TLDiff = decltype(Private::diff(std::declval<TL>()));

        // Internal helpers

        /** A struct to hold the private member functions of TypeList while still allowing
         *  static access among other things; i.e. make them psuedo private
         */
        struct Private {
            /** Return a TypeList containing Args... set minus the types in Remove
             *  The argument forces that its input is a typelist
             *  Note: This function must be called only in an unevaluated context
             */
            template <typename... Remove> static auto diff(TypeList<Remove...> &&) {
                if constexpr (sizeof...(Remove) == 0 || sizeof...(Args) == 0) {
                    return std::declval<TypeList<Args...>>(); // Nothing to remove
                }
                else {
                    return diff_helper<TypeList<Remove...>, Args...>(); // Remove items from Args
                }
            }

            /** A helper of diff which assumes len(Args) > 0
             *  Note: This function must be called only in an unevaluated context
             */
            template <typename RemoveTL, typename Head, typename... Tail>
            static auto diff_helper() {
                // Either an empty TypeList or a list containing only Head
                UTIL_CCBOOL no_head_out { RemoveTL::template contains<Head> };
                // Base case
                if constexpr (sizeof...(Tail) == 0) {
                    // Either return an empty typelist of a typelist just containing Head
                    using Ret = std::conditional_t<no_head_out, TypeList<>, TypeList<Head>>;
                    return std::declval<Ret>(); // Tail is empty so return
                }
                // Recursive step
                else {
                    using TailOut = decltype(diff_helper<RemoveTL, Tail...>());
                    // Either prepend head or not depending on if it is in RemoveTL
                    if constexpr (no_head_out) {
                        return std::declval<TailOut>(); // Head is empty
                    }
                    else {
                        using Ret = typename TailOut::template Prepend<Head>; // Head out + Tail out
                        return std::declval<Ret>();
                    }
                }
            }
        };
    };

} // namespace Util

#endif
