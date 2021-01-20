/**
 * @file
 * @brief This file defines the Expression cast functions
 */
#ifndef __EXPRESSION_CAST_HPP__
#define __EXPRESSION_CAST_HPP__

#include "private/raw.hpp"

#include "../utils.hpp"

#include <memory>
#include <type_traits>


namespace Expression {

    // Forward declarations
    namespace Raw {
        class Base;
    }

    /** This function is used to statically up-cast between Expression types
     *  Normal dynamic casting will not work on because shared pointers are not subclasses of each
     *  other like their template arguments are.
     *  Since we are up-casting, this is staticlly typesafe
     */
    template <typename To, typename From> To up_cast(const From &f) noexcept {
        using RawTo = Private::Raw<To>;
        using RawFrom = Private::Raw<From>;
        static_assert(std::is_base_of<Raw::Base, RawTo>::value, "To must derive from Base");
        static_assert(std::is_base_of<RawTo, RawFrom>::value, "From must derive from To");
        return std::static_pointer_cast<RawTo>(f);
    }

    /** This function is used to dynamically down-cast between Expression types
     *  Normal dynamic casting will not work on because shared pointers are not subclasses of each
     *  other like their template arguments are.
     *  std::bad_cast should never be thrown due to our static_assert and the fact that these are
     * pointers
     *  Note: Since we are down-casting, we dynamic_cast
     */
    template <typename To, typename From> To down_cast(const From &f) noexcept {
        using RawTo = Private::Raw<To>;
        using RawFrom = Private::Raw<From>;
        static_assert(std::is_base_of<Raw::Base, RawFrom>::value, "From must derive from Base");
        static_assert(std::is_base_of<RawFrom, RawTo>::value, "To must derive from From");
        return std::dynamic_pointer_cast<RawTo>(f);
    }

    /** This function extends Expression::cast by throwing a BadCast exception on failure
     *  std::bad_cast should never be thrown due to our static_assert and the fact that these are
     *pointers
     *  This function demands that f != nullptr
     *  Note: Since we are down-casting, we dynamic_cast
     */
    template <typename To, typename From> To down_cast_throw_on_fail(const From &f) {
        Utils::affirm<Utils::Error::Unexpected::IncorrectUsage>(
            f != nullptr, __func__, " called with incorrect usage: f == nullptr",
            "\tFile: " __FILE__ "\n\tLine: " MACRO_TO_STRING(__LINE__));
        To ret = down_cast<To>(f);
        Utils::affirm<Utils::Error::Unexpected::BadCast>(ret, WHOAMI
                                                         " -- dynamic_pointer_cast failed.");
        return ret;
    }

} // namespace Expression

#endif
