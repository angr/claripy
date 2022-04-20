/**
 * @file
 * \ingroup util
 * @brief This file defines type map type
 */
#ifndef R_SRC_UTIL_TYPE_MAP_HPP_
#define R_SRC_UTIL_TYPE_MAP_HPP_

#include "is.hpp"
#include "list.hpp"
#include "pair.hpp"


namespace Util::Type {

    /** An uninstantiable type bi-directional map class
     *  Warning: This map may drop type qualifiers
     *  Warning: Duplicate mappings may lead to undefined behavior
     */
    template <typename... Args> struct Map : public Unconstructable {
        struct Private; // Forward declare

        // Representation

        /** Get the keys from the input */
        using Keys = typename Private::template Half<true>;
        /** Get the keys from the input */
        using Values = typename Private::template Half<false>;
        static_assert(Keys::len == Values::len, "Should be equal");

        // Bools

        /** Return true if T is in the map */
        template <typename T>
        static UTIL_ICCBOOL contains { Keys::template contains<T> || Values::template contains<T> };

        // Getters

        /** Key -> Value */
        template <typename T> using GetValue = typename Private::template Getter<T, Values, Keys>;
        /** Value -> Key */
        template <typename T> using GetKey = typename Private::template Getter<T, Keys, Values>;
        /** A getter, will check keys and values, cannot be used if T exists in both */
        template <typename T>
        using Get = std::remove_pointer_t<decltype(Private::template get<T>())>;

        // Map Generators

        /** Get a type map with the key-value pair added */
        template <typename Key, typename Value> using Add = Map<Args..., Key, Value>;

        /** A struct to hold the private member functions of Map while still allowing
         *  static access among other things; i.e. make them psuedo private
         */
        struct Private {
            /** Split TL into two Lists of alternating types
             *  We return pointers to the type lists since declval won't work here
             */
            template <bool Left, typename TL> static constexpr auto half() {
                static_assert(TL::len % 2 == 0, "There must be an even number of input types");
                static_assert(Is::container<List, TL>, "TL must be a type list");
                // Base Case
                if constexpr (TL::len == 0) {
                    return (List<> *) { nullptr };
                }
                // Recursive case
                else {
                    // Tail = TL[2:].prepend(Left ? TL[0] : TL[1])
                    using Head = typename TL::template Get<Left ? 0 : 1>;
                    using PopFrontTwo = typename TL::template Pop<2>;
                    using Tail = std::remove_pointer_t<decltype(half<Left, PopFrontTwo>())>;
                    return (typename Tail::template Prepend<Head> *) { nullptr };
                }
            }

            /** Get half of the Args */
            template <bool Left>
            using Half = std::remove_pointer_t<decltype(half<Left, List<Args...>>())>;

            /** Get T from Out using the Index found from In */
            template <typename T, typename Out, typename In>
            using Getter = typename Out::template Get<In::template find<T>>;

            /** A getter, will check keys and values, cannot be used if T exists in both
             *  We return pointers here since we can't use declval
             */
            template <typename T> static constexpr auto get() {
                UTIL_CCBOOL is_key { Keys::template contains<T> };
                UTIL_CCBOOL is_value { Values::template contains<T> };
                // Safety
                static_assert(is_key || is_value, "T is not anywhere in this map");
                static_assert(!is_key || !is_value,
                              "T is both a key and a value; use either GetKey or GetValue");
                // Return desired type
                if constexpr (is_key) {
                    return (GetValue<T> *) { nullptr };
                }
                else {
                    return (GetKey<T> *) { nullptr };
                }
            }
        };
    };

} // namespace Util::Type

#endif
