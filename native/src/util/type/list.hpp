/**
 * @file
 * \ingroup util
 * @brief This file defines type list type
 */
#ifndef R_SRC_UTIL_TYPE_LIST_HPP_
#define R_SRC_UTIL_TYPE_LIST_HPP_

#include "unconstructable.hpp"

#include "../../constants.hpp"
#include "../macros.hpp"


namespace Util::Type {

    /** An uninstantiable type list class
     *  Warning: This list may drop type qualifiers
     */
    template <typename... Args> struct List : public Unconstructable {
        struct Private; // Forward declare

        /** Allow copy construction in unevaluated contexts */
        List(const List &);

        // Conversions

        /** The type of this list */
        using This = List<Args...>;

        /** Return a Container<Args..., Other...> */
        template <template <typename...> typename Container, typename... Other>
        using ApplyWith = Container<Args..., Other...>;

        /** Return a Container<Args...> */
        template <template <typename...> typename Container> using Apply = Container<Args...>;

        // Getters

        /** Returns the length of the typelist */
        static inline constexpr const U64 len { sizeof...(Args) };

        /** Returns a pointer to the type to get */
        template <U64 I, typename Head, typename... Tail> static constexpr auto get_helper() {
            static_assert(I < len, "Get index out of bounds");
            if constexpr (I == 0) {
                return (Head *) { nullptr }; // Can't use declval here :(
            }
            else {
                return get_helper<I - 1, Tail...>();
            }
        }

        /** Returns the i'th element of the typelist */
        template <U64 i> using Get = std::remove_pointer_t<decltype(get_helper<i, Args...>())>;

        /** Returns the index of T in Args...
         *  Requires T in Args...
         */
        template <typename T, bool ignore_cv = false>
        static inline constexpr const U64 find { Private::template find<T, ignore_cv>() };

        // List generators

        /** Return List<Other..., Args...> */
        template <typename... Other> using Prepend = List<Other..., Args...>;

        /** Return List<Args..., Other...> */
        template <typename... Other> using Append = List<Args..., Other...>;

        /** Pop Front */
        using PopFront = typename Private::PopFront;

        /** Pop front n items */
        template <U64 N> using Pop = typename Private::template Pop<N>;

        /** Return true if T in Args */
        template <typename T, bool ignore_cv = false>
        static UTIL_ICCBOOL contains { (Private::template is_same<T, Args, ignore_cv> || ...) };

        /** Return a List containing Args... set minus the types in the type list TL */
        template <typename TL> using TLDiff = decltype(Private::diff(std::declval<TL>()));

        // Internal helpers

        /** A struct to hold the private member functions of List while still allowing
         *  static access among other things; i.e. make them psuedo private
         */
        struct Private {

            // Note: there are much cleaner ways to do a lot of this, however this
            // way should be fully in spec and doesn't rely on a 'nice' compiler

            /** Return true if T == U */
            template <typename T, typename U, bool ignore_cv>
            static UTIL_ICCBOOL is_same { std::is_same_v<T, U> ||
                                          (ignore_cv &&
                                           std::is_same_v<std::remove_cv<T>, std::remove_cv<U>>) };

            /** Return List<X...> */
            template <typename, typename... X> struct Split { using Tail = List<X...>; };

            /** Returns a List<Args[1:]...>*
             *  We use a function instead of a struct here since we are
             *  not at namespace scope and thus cannot do specializations
             *  Note: we use List<> *'s here since List<> hasn't been fully defined yet
             */
            template <U64 N> static constexpr auto pop_front_helper() {
                if constexpr (N == 0) {
                    return (List<> *) { nullptr };
                }
                else {
                    using Tail = typename Split<Args...>::Tail;
                    return (Tail *) { nullptr };
                }
            };

            /** List<Args[1:]...> */
            using PopFront = std::remove_pointer_t<decltype(pop_front_helper<len>())>;

            /** Pop multiple items
             *  We use a function instead of a struct here since we are
             *  not at namespace scope and thus cannot do specializations
             *  Note: we use List<> *'s here since List<> hasn't been fully defined yet
             * */
            template <U64 N> static constexpr auto pop() {
                if constexpr (N == 0) {
                    return (This *) { nullptr };
                }
                else if constexpr (N == 1) {
                    return (PopFront *) { nullptr };
                }
                else {
                    return PopFront::Private::template pop<N - 1>();
                }
            }

            /** PopFront */
            template <U64 N> using Pop = std::remove_pointer_t<decltype(pop<N>())>;

            /** Return the index of T in Args...
             *  Requires T in Args...
             */
            template <typename T, bool ignore_cv> static constexpr U64 find() {
                static_assert(contains<T, ignore_cv>, "T is not in X");
                if constexpr (Private::is_same<Get<0>, T, ignore_cv>) {
                    return 0;
                }
                else {
                    return 1 + PopFront::template find<T>;
                }
            }

            /** Return a List containing Args... set minus the types in Remove
             *  The argument forces that its input is a typelist
             *  Note: This function must be called only in an unevaluated context
             */
            template <typename... Remove> static auto diff(List<Remove...> &&) {
                if constexpr (sizeof...(Remove) == 0 || len == 0) {
                    return std::declval<This>(); // Nothing to remove
                }
                else {
                    return diff_helper<List<Remove...>, Args...>(); // Remove items from Args
                }
            }

            /** A helper of diff which assumes len(Args) > 0
             *  Note: This function must be called only in an unevaluated context
             */
            template <typename RemoveTL, typename Head, typename... Tail>
            static auto diff_helper() {
                // Either an empty List or a list containing only Head
                UTIL_CCBOOL no_head_out { RemoveTL::template contains<Head> };
                // Base case
                if constexpr (sizeof...(Tail) == 0) {
                    // Either return an empty typelist of a typelist just containing Head
                    using Ret = std::conditional_t<no_head_out, List<>, List<Head>>;
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

} // namespace Util::Type

#endif
