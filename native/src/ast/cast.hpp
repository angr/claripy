/**
 * @file
 * @brief This file defines the AST::cast function and related functions
 */
#ifndef __AST_CAST_HPP__
#define __AST_CAST_HPP__

#include "base.hpp"

#include "../errors/unexpected.hpp"
#include "../utils/affirm.hpp"

#include <type_traits>


/** A namespace used for the ast directory */
namespace AST {

    /** This function is used to cast between AST types
     *  Normal dynamic casting will not work on because shared pointers are not subclasses of each
     * other like their template arguments are
     */
    template <typename To, typename From> To cast(From &f) {
        static_assert(std::is_base_of<To, From>::value || std::is_base_of<From, To>::value,
                      "From and To must be ancestors and kin of each other");

        // Deduce the AST::Cached type the shared pointer type T contains
        using Internal = decltype(std::declval<To>().get());
        using Cached = typename std::remove_pointer<Internal>::type;

        // Cast
        To ret = std::dynamic_pointer_cast<To>(f);

        // Return on success
        return ret;
    }

    /** This function extends AST::cast by throwing a BadCast exception on failure */
    template <typename To, typename From> To cast_throw_on_fail(From &f) {
        To ret = cast<To>(f);
        Utils::affirm<Errors::Unexpected::BadCast>(
            ret, __FILE__
            ": " MACRO_TO_STRING(__LINE__) ": dynamic_pointer_cast within AST::factory failed.");
        return ret;
    }

} // namespace AST

#endif
