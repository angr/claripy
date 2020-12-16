/**
 * @file bool.hpp
 * @brief This file defines the AST::Cached::Bool class and defines AST::Bool
 */
#ifndef __AST_BOOL_HPP__
#define __AST_BOOL_HPP__

#include "using_declarations.hpp"

#include "base.hpp"


/** A namespace used for the ast directory */
namespace AST {

    /** A namespace to denote self-caching classes
     *  These classes are unlikely to be accessed directly, but rather should be accessed via a
     * shared_ptr
     */
    namespace Cached {

        /** This class represents an AST boolean */
        class Bool : public Base {
          public:
            /** Return true if the AST evaluates to true */
            bool is_true() const;

            /** Return true if the AST evaluates to false */
            bool is_false() const;
        };
    } // namespace Cached

    /** An abbreviation for a shared pointer to the cached bool class */
    using Bool = std::shared_ptr<Cached::Bool>;

} // namespace AST

#endif
