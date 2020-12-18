/**
 * @file
 * @brief This file defines many useful using statements within AST
 * For example, AST::Base is defined as std::shared_ptr<AST::RawTypes::Base>
 */
#ifndef __AST_USING_DECLARATIONS_HPP__
#define __AST_USING_DECLARATIONS_HPP__

#include <memory>


/** A namespace used for the ast directory */
namespace AST {

    /** A namespace which contains self-caching classes and things related to AST caching
     *  These classes are unlikely to be accessed directly, but rather should be accessed via a
     * shared_ptr
     */
    namespace RawTypes {
        // Forward declare classes
        class Base;
        class Bool;
        class Bits;
        class String;
        class Int;
        class VS;
        class BV;
    } // namespace RawTypes

    // Define shared pointer abbreviations

    /** An abbreviation for a shared pointer to the cached Base class */
    using Base = std::shared_ptr<RawTypes::Base>;

    /** An abbreviation for a shared pointer to the cached Bool class */
    using Bool = std::shared_ptr<RawTypes::Bool>;

    /** An abbreviation for a shared pointer to the cached Bits class */
    using Bits = std::shared_ptr<RawTypes::Bits>;

    /** An abbreviation for a shared pointer to the cached BV class */
    using BV = std::shared_ptr<RawTypes::BV>;

    /** An abbreviation for a shared pointer to the cached VS class */
    using VS = std::shared_ptr<RawTypes::VS>;

    /** An abbreviation for a shared pointer to the cached String class */
    using String = std::shared_ptr<RawTypes::String>;

    /** An abbreviation for a shared pointer to the cached Int class */
    using Int = std::shared_ptr<RawTypes::Int>;

} // namespace AST

#endif
