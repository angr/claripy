/**
 * @file
 * \ingroup util
 * @brief This file defines LazyStr which lazily converts Args && ... args to an std::string
 */
#ifndef R_SRC_UTIL_LAZYSTR_HPP_
#define R_SRC_UTIL_LAZYSTR_HPP_

#include "assert.hpp"
#include "err.hpp"
#include "to_str.hpp"
#include "type.hpp"

namespace Util {

    /** The abstract LazyStr class */
    struct LazyStr {
        /** The string functor */
        virtual std::string operator()() = 0;
        /** Constructor */
        inline LazyStr() noexcept = default;
        /** Destructor */
        virtual inline ~LazyStr() noexcept {}
        // Disable other implicits
        SET_IMPLICITS_NONDEFAULT_CTORS(LazyStr, delete);
    };

    /** The concrete LazyStr class */
    template <typename... Args> class ConcreteLazyStr final : public LazyStr {
        SET_IMPLICITS_NONDEFAULT_CTORS(ConcreteLazyStr, delete);

      public:
        /** The type this class stores its arguments in */
        using Tuple = std::tuple<Args...>;

        /** Constructor */
        explicit inline ConcreteLazyStr(Tuple &&tup) noexcept
            : LazyStr(), data { std::move(tup) } {}

        /** Destructor */
        inline ~ConcreteLazyStr() noexcept {}

        /** Output as a string */
        inline std::string operator()() final {
            if (std::holds_alternative<Tuple>(data)) {
                data = std::apply(Util::to_str<Args...>, std::move(std::get<Tuple>(data)));
            }
            return std::get<std::string>(data);
        }

      private:
        /** The stored data */
        std::variant<std::string, Tuple> data;
    };

} // namespace Util
#endif