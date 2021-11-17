/**
 * @file
 * \ingroup util
 * @brief This file defines type map type
 */
#ifndef R_UTIL_TYPE_MAP_HPP_
#define R_UTIL_TYPE_MAP_HPP_

#include "list.hpp"
#include "pair.hpp"

#include "../is_x.hpp"


namespace Util::Type {

    /** An uninstantiable type map class
     *  Warning: This map may drop type qualifiers
     */
    template <typename... Args> struct Map : public Unconstructable {
        struct Private; // Forward declare

        // Representation

        /** Get the keys from the input */
        using Keys = typename Private::template Half<true>;
        /** Get the keys from the input */
        using Values = typename Private::template Half<false>;
        static_assert(Keys::len == Values::len, "Should be equal");

        // Getters

        /** Key -> Value */
        template <typename T> using GetValue = typename Private::template Getter<T, Values, Keys>;
        /** Value -> Key */
        template <typename T> using GetKey = typename Private::template Getter<T, Keys, Values>;

        /** A struct to hold the private member functions of Map while still allowing
         *  static access among other things; i.e. make them psuedo private
         */
        struct Private {
            /** Split TL into two Lists of alternating types */
            template <bool Left, typename TL> static constexpr auto half() {
                static_assert(TL::len % 2 == 0, "There must be an even number of input types");
                static_assert(Util::is_x<List, TL>, "TL must be a type list");
                // Base Case
                if constexpr (TL::len == 0) {
                    return std::declval<List<>>();
                }
                // Recursive case
                else {
                    // Tail = TL[2:].prepend(Left ? TL[0] : TL[1])
                    using Head = typename TL::template Get<Left ? 0 : 1>;
                    using Tail = decltype(half<Left, typename TL::template Pop<2>>());
                    return std::declval<typename Tail::template Prepend<Head>>();
                }
            }
            /** Get half of the Args */
            template <bool Left> using Half = decltype(half<Left, List<Args...>>());
            /** Get T from Out using the Index found from In */
            template <typename T, typename Out, typename In>
            using Getter = typename Out::template Get<In::template find<T>>;
        };
    };

} // namespace Util::Type

#endif
