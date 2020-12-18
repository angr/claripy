/**
 * @file
 * @brief This file defines many useful using statements within AST
 * For example, AST::Base is defined as std::shared_ptr<AST::RawTypes::Base>
 */
#ifndef __AST_FORWARD_DECLARATIONS_HPP__
#define __AST_FORWARD_DECLARATIONS_HPP__

#include "macros.hpp"

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
    DEFINE_NON_RAW_TYPE(Base)
    DEFINE_NON_RAW_TYPE(Bool)
    DEFINE_NON_RAW_TYPE(Bits)
    DEFINE_NON_RAW_TYPE(BV)
    DEFINE_NON_RAW_TYPE(VS)
    DEFINE_NON_RAW_TYPE(String)
    DEFINE_NON_RAW_TYPE(Int)

} // namespace AST

#endif
