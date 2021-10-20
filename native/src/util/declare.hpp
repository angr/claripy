/**
 * @file
 * \ingroup util
 * @brief Defines a way of declaring a stack variable without invoking the constructor
 */
#ifndef R_UTIL_DECLARE_HPP_
#define R_UTIL_DECLARE_HPP_

#include "../macros.hpp"

#include <memory>


namespace Util {

    /** A type which contains but does not initialize a T
     *  Destructs value when unions goes out of scope only if Destruct
     *  Note: This is a raw union, std::variant and such would not work
     */
    template <typename T, bool Destruct> union Declare {

        /** Empty constructor */
        Declare() noexcept {} // NOLINT (this is a union, default is incorrect)

        /** Destructor */
        ~Declare() noexcept(!Destruct || noexcept(~T())) {
            if constexpr (Destruct) {
                value.~T();
            }
        }

        /** Contained T */
        T value;

        // Disable other form of construction
        // This is implicit if T is not trivial
        SET_IMPLICITS_EXCLUDE_DEFAULT_CTOR(Declare, delete);
    };

} // namespace Util

#endif
