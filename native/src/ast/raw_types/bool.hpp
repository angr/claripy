/**
 * @file
 * @brief This file defines the AST::RawTypes::Bool class and defines AST::Bool
 */
#ifndef __AST_RAWTYPES_BOOL_HPP__
#define __AST_RAWTYPES_BOOL_HPP__

#include "base.hpp"


/** A namespace used for the ast directory */
namespace AST {

    /** A namespace which contains the raw AST types that are constructed via AST::factory
     *  These classes are unlikely to be accessed directly, but rather should be via a shared_ptr
     */
    namespace RawTypes {

        /** This class represents an AST boolean */
        class Bool : public Base {
            AST_RAWTYPES_INIT_AST_BASE_SUBCLASS(Bool)
          public:
            /** Return true if the AST evaluates to true */
            bool is_true() const;

            /** Return true if the AST evaluates to false */
            bool is_false() const;

          private:
            /** A private constructor to disallow public creation
             *  This must have take in the same arguments as the hash function, minus the hash
             *  which must be the first argument passed
             */
            Bool(const Hash h, const Ops::Operation o);

            /** The hash function of this AST
             *  This must have take in the same arguments as the constructor, minus the hash
             * @todo not exactly, args in the constructor can consume inputs
             */
            static Hash hash(const Ops::Operation o);
        };

    } // namespace RawTypes

} // namespace AST

#endif
