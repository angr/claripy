/**
 * @file using_declarations.hpp
 * @brief This file defines many useful using statements within AST
 * For example, AST::Base is defined as std::shared_ptr<AST::Cached::Base>
 */
#ifndef __AST_USING_DECLARATIONS_HPP__
#define __AST_USING_DECLARATIONS_HPP__

#include <memory>


/** A namespace used for the ast directory */
namespace AST {

    /** A namespace to denote self-caching classes
     *  These classes are unlikely to be accessed directly, but rather should be accessed via a
     * shared_ptr
     */
    namespace Cached {

        // Forward declare classes
        class Base;
        class Bool;
    } // namespace Cached

    // Define shared pointer abbreviations

    /** An abbreviation for a shared pointer to the cached base class */
    using Base = std::shared_ptr<Cached::Base>;

    /** An abbreviation for a shared pointer to the cached base class */
    using Bool = std::shared_ptr<Cached::Bool>;

} // namespace AST

#endif
