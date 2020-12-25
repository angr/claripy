/**
 * @file
 * @brief This file defines the AST::cast function and related functions
 */
#ifndef __AST_CAST_HPP__
#define __AST_CAST_HPP__

#include "private/raw.hpp"

#include "../utils.hpp"

#include <memory>
#include <type_traits>


namespace AST {

    // Forward declarations
    namespace RawTypes {
        class Base;
    }

    /** This function is used to statically up-cast between AST types
     *  Normal dynamic casting will not work on because shared pointers are not subclasses of each
     *  other like their template arguments are.
     *  Since we are up-casting, this is staticlly typesafe
     */
    template <typename To, typename From> To up_cast(const From &f) noexcept {
        using RawTo = Private::Raw<To>;
        using RawFrom = Private::Raw<From>;
        static_assert(std::is_base_of<RawTypes::Base, RawTo>::value, "To must derive from Base");
        static_assert(std::is_base_of<RawTo, RawFrom>::value, "From must derive from To");
        return std::static_pointer_cast<RawTo>(f);
    }

    /** This function is used to dynamically down-cast between AST types
     *  Normal dynamic casting will not work on because shared pointers are not subclasses of each
     *  other like their template arguments are.
     *  std::bad_cast should never be thrown due to our static_assert and the fact that these are
     * pointers
     *  Note: Since we are down-casting, we dynamic_cast
     */
    template <typename To, typename From> To down_cast(const From &f) noexcept {
        using RawTo = Private::Raw<To>;
        using RawFrom = Private::Raw<From>;
        static_assert(std::is_base_of<RawTypes::Base, RawFrom>::value,
                      "From must derive from Base");
        static_assert(std::is_base_of<RawFrom, RawTo>::value, "To must derive from From");
        return std::dynamic_pointer_cast<RawTo>(f);
    }

    /** This function extends AST::cast by throwing a BadCast exception on failure
     *  std::bad_cast should never be thrown due to our static_assert and the fact that these are
     *pointers
     *  This function demands that f != nullptr
     *  Note: Since we are down-casting, we dynamic_cast
     *	@todo Improve error message
     */
    template <typename To, typename From> To down_cast_throw_on_fail(const From &f) {
        Utils::affirm<Utils::Error::Unexpected::IncorrectUsage>(
            f != nullptr, __func__, " called with incorrect usage: f == nullptr",
            "\tFile: " __FILE__ "\n\tLine: " MACRO_TO_STRING(__LINE__));
        To ret = down_cast<To>(f);
        Utils::affirm<Utils::Error::Unexpected::BadCast>(
            ret,
            "dynamic_pointer_cast within AST::factory failed.\n"
            "\tFile: " __FILE__ "\n\tLine: ",
            __LINE__, "\n\t", __func__);
        return ret;
    }

} // namespace AST

#endif
