/**
 * @file
 * @brief This file defines the AST::Cached::String class and defines AST::String
 */
#ifndef __AST_STRING_HPP__
#define __AST_STRING_HPP__

#include "../macros.hpp"

#include "bits.hpp"


/** A namespace used for the ast directory */
namespace AST {

    /** A namespace to denote self-caching classes
     *  These classes are unlikely to be accessed directly, but rather should be accessed via a
     * shared_ptr
     */
    namespace Cached {

        /** An AST representing a string */
        class String : public Bits {

            /** Create a concrete String
             *  @todo kwargs
             */
            /* static ::AST::String Concrete(const std::string & value, const Constants::Int
             * length); */

            /** Return the name of the type this class represents irrespective of length */
            std::string fundamental_type_name() const;

            /** Delete all default constructors */
            DELETE_DEFAULTS(String);
        };
    } // namespace Cached
} // namespace AST

#endif
