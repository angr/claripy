/**
 * @file
 * @brief This file defines the AST::Cached::BV class and defines AST::BV
 */
#ifndef __AST_BV_HPP__
#define __AST_BV_HPP__

#include "using_declarations.hpp"

#include "bits.hpp"


/** A namespace used for the ast directory */
namespace AST {

    /** A namespace to denote self-caching classes
     *  These classes are unlikely to be accessed directly, but rather should be accessed via a
     * shared_ptr
     */
    namespace Cached {

        /** This class represents an AST bit vector */
        class BV : public Bits {
          public:
        };
    } // namespace Cached

    /** An abbreviation for a shared pointer to the cached bv class */
    using BV = std::shared_ptr<Cached::BV>;

} // namespace AST

#endif
