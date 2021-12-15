/**
 * @file
 * \ingroup util
 * @brief This file defines LazyStr which lazily converts Args && ... args to an std::string
 */
#ifndef R_UTIL_LAZYSTR_HPP_
#define R_UTIL_LAZYSTR_HPP_

#include "assert.hpp"
#include "err.hpp"
#include "to_str.hpp"
#include "type.hpp"

namespace Util {

    /** The abstract LazyStr class
     *  Note: operator() may only be called once!
     */
    struct LazyStr {
        /** The string functor; may only be called once */
        virtual std::string operator()() = 0;
        /** Constructor */
        inline LazyStr() noexcept = default;
        /** Destructor */
        virtual inline ~LazyStr() noexcept {}
        // Disable other implicits
        SET_IMPLICITS_NONDEFAULT_CTORS(LazyStr, delete);

      protected:
        /** Used to denote if () has been called */
        bool done { false };
    };

    /** The concrete LazyStr class
     *  Note: operator() may only be called once!
     */
    template <typename... Args> class ConcreteLazyStr final : public LazyStr {
        SET_IMPLICITS_NONDEFAULT_CTORS(ConcreteLazyStr, delete);

      public:
        /** The type this class stores its arguments in */
        using Tuple = std::tuple<Args...>;

        /** Constructor */
        inline ConcreteLazyStr(Tuple &&tup) noexcept : LazyStr(), data { std::move(tup) } {}

        /** Destructor */
        inline ~ConcreteLazyStr() noexcept {}

        /** Output as a string; may only be called once */
        inline std::string operator()() final {
            // Once check
            UTIL_ASSERT(Util::Err::Usage, !done,
                        "LazyStr() may only be called once as it consumes its data");
            done = true;
            return std::apply(Util::to_str<Args...>, std::move(data));
        }

      private:
        /** The stored data */
        Tuple data;
    };

} // namespace Util
#endif