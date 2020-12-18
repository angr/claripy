/**
 * @file
 * @brief This file defines the AST::cast function and related functions
 */
#ifndef __AST_CAST_HPP__
#define __AST_CAST_HPP__

#include "../errors/unexpected.hpp"
#include "../utils/affirm.hpp"

#include <memory>
#include <type_traits>


/** A namespace used for the ast directory */
namespace AST {

    // Forward declarations
    namespace RawTypes {
        class Base;
    }

    /** This function is used to cast between AST types
     *  Normal dynamic casting will not work on because shared pointers are not subclasses of each
     *  other like their template arguments are.
     *  std::bad_cast should never be thrown due to our static_assert and the fact that these are
     * pointers
     */
    template <typename To, typename From>
    inline std::shared_ptr<To> cast(std::shared_ptr<From> &f) {

        // Static verification
        static_assert(std::is_base_of<RawTypes::Base, To>::value, "To must derive from Base");
        static_assert(std::is_base_of<RawTypes::Base, From>::value, "From must derive from Base");
        static_assert(std::is_base_of<To, From>::value || std::is_base_of<From, To>::value,
                      "From and To must be ancestors and kin of each other");

#if DEBUG
        return std::dynamic_pointer_cast<To>(std::forward<From>(f));
#else
        return std::static_pointer_cast<To>(std::forward<std::shared_ptr<From>>(f));
#endif
    }

    /** This function extends AST::cast by throwing a BadCast exception on failure
     *  std::bad_cast should never be thrown due to our static_assert and the fact that these are
     *pointers
     *	@todo Improve error message
     */
    template <typename To, typename From>
    inline std::shared_ptr<To> cast_throw_on_fail(std::shared_ptr<From> &f) {
        To ret = cast<To>(std::forward<From>(f));
        Utils::affirm<Errors::Unexpected::BadCast>(
            "dynamic_pointer_cast within AST::factory failed.\n"
            "\tFile: " __FILE__ "\n\tLine: " __LINE__ "\n\t",
            __func__);
        return ret;
    }

} // namespace AST

#endif
