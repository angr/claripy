/**
 * @file
 * @brief This file defines the AST::Cached::Int class and defines AST::Int
 */
#ifndef __AST_INT_HPP__
#define __AST_INT_HPP__

#include "../macros.hpp"

#include "base.hpp"


/** A namespace used for the ast directory */
namespace AST {

    /** A namespace to denote self-caching classes
     *  These classes are unlikely to be accessed directly, but rather should be accessed via a
     * shared_ptr
     */
    namespace Cached {

        /** An AST representing an integer */
        class Int : public Base {

            /** Return the name of the type this class represents */
            std::string type_name() const;

            /** Delete all default constructors */
            DELETE_DEFAULTS(Int);
        };
    } // namespace Cached
} // namespace AST

#endif
