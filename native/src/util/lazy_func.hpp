/**
 * @file
 * \ingroup util
 * @brief This file defines a lazily evaluated function wrapper
 */
#ifndef R_SRC_UTIL_LAZYFUNC_HPP_
#define R_SRC_UTIL_LAZYFUNC_HPP_

#include <ostream>
#include <tuple>

namespace Util {

    /** A lazily evaluated function wrapper */
    template <typename Func, typename... Args> class LazyFunc {
        /** Return type */
        using Ret = std::invoke_result_t<Func, Args &&...>;
        /** Tuple type */
        using Tuple = std::tuple<Args...>;
        /** Pair type */
        using Pair = std::pair<Func, Tuple>;
        /** Args */
        mutable std::variant<Ret, Pair> data;

      public:
        /** Constructor */
        constexpr LazyFunc(Func &&f, Tuple &&args) noexcept
            : data { Pair { std::move(f), std::move(args) } } {}
        /** Constructor */
        constexpr LazyFunc(Func &&f, Args &&...args) noexcept
            : data { Pair { std::move(f), Tuple { std::forward<Args>(args)... } } } {}

        /** Evaluate func(std::forward<Args>(args)...) */
        constexpr inline Ret operator()() const {
            if (std::holds_alternative<Pair>(data)) {
                auto &[f, args] = std::get<Pair>(data);
                data = std::apply(f, std::move(args));
            }
            return std::get<Ret>(data);
        };
    };

    /** A lazily evaluate function wrapper */
    template <typename Func> class LazyFunc<Func> {
        /** Return type */
        using Ret = std::invoke_result_t<Func>;
        /** Func */
        mutable std::variant<Ret, Func> data;

      public:
        /** Constructor */
        constexpr LazyFunc(Func &&f) noexcept : data { std::move(f) } {}
        /** Eval func() */
        constexpr inline Ret operator()() const {
            if (std::holds_alternative<Func>(data)) {
                data = std::get<Func>(data)();
            }
            return std::get<Ret>(data);
        };
    };

    /** Consuming << operator
     *  Warning: This consumes args, do not call it multiple times
     */
    template <typename... Args>
    constexpr std::ostream &operator<<(std::ostream &o, const Util::LazyFunc<Args...> &l) {
        return o << l();
    }

} // namespace Util

#endif
