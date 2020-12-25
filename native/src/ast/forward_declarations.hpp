/**
 * @file
 * @brief This file defines many useful using statements within AST
 * For example, AST::Base is defined as std::shared_ptr<AST::RawTypes::Base>
 * @todo disable shared_ptr.get() ?
 */
#ifndef __AST_FORWARD_DECLARATIONS_HPP__
#define __AST_FORWARD_DECLARATIONS_HPP__

#include "macros.hpp"

#include <memory>


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
    AST_DECLARE_AND_DEFINE_NON_RAW_TYPE(Base)
    AST_DECLARE_AND_DEFINE_NON_RAW_TYPE(Bool)
    AST_DECLARE_AND_DEFINE_NON_RAW_TYPE(Bits)
    AST_DECLARE_AND_DEFINE_NON_RAW_TYPE(BV)
    AST_DECLARE_AND_DEFINE_NON_RAW_TYPE(VS)
    AST_DECLARE_AND_DEFINE_NON_RAW_TYPE(String)
    AST_DECLARE_AND_DEFINE_NON_RAW_TYPE(Int)

} // namespace AST

#endif
