/**
 * @file
 * @brief This file defines the AST::Cached::VS class and defines AST::VS
 */
#ifndef __AST_VS_HPP__
#define __AST_VS_HPP__

#include "../macros.hpp"

#include "bits.hpp"


/** A namespace used for the ast directory */
namespace AST {

    /** A namespace to denote self-caching classes
     *  These classes are unlikely to be accessed directly, but rather should be accessed via a
     * shared_ptr
     */
    namespace Cached {

        /** An AST representing a value set */
        class VS : public Bits {

            /** Return the name of the type this class represents irrespective of length */
            std::string fundamental_type_name() const;

            /** Delete all default constructors */
            DELETE_DEFAULTS(VS);
        };
    } // namespace Cached
} // namespace AST

#endif
