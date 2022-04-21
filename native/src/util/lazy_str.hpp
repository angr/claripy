/**
 * @file
 * \ingroup util
 * @brief This file defines LazyStr which lazily converts Args && ... args to an std::string
 */
#ifndef R_SRC_UTIL_LAZYSTR_HPP_
#define R_SRC_UTIL_LAZYSTR_HPP_

#include "lazy_func.hpp"
#include "to_str.hpp"

namespace Util {

    /** The abstract LazyStr class */
    struct LazyStr {
        /** The string functor */
        virtual std::string operator()() = 0;
        /** Constructor */
        constexpr LazyStr() noexcept = default;
        /** Destructor */
        virtual inline ~LazyStr() noexcept {}
        // Disable other implicits
        SET_IMPLICITS_NONDEFAULT_CTORS(LazyStr, delete);
    };

    /** The concrete LazyStr class */
    template <typename... Args> class ConcreteLazyStr final : public LazyStr {
        /** Alias of to_str */
        static constexpr const auto to_str { Util::to_str<Args...> };
        /** Lazy function */
        LazyFunc<decltype(to_str), Args...> lazy;

      public:
        /** Constructor */
        explicit constexpr ConcreteLazyStr(std::tuple<Args...> &&tup) noexcept
            : lazy { std::move(to_str), std::move(tup) } {}
        /** Destructor */
        inline ~ConcreteLazyStr() noexcept {}
        /** Output as a string */
        inline std::string operator()() { return lazy(); }
    };

} // namespace Util
#endif