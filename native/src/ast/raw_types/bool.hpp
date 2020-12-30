/**
 * @file
 * @brief This file defines the AST::RawTypes::Bool class and defines AST::Bool
 */
#ifndef __AST_RAWTYPES_BOOL_HPP__
#define __AST_RAWTYPES_BOOL_HPP__

#include "base.hpp"


namespace AST {

    // These types should be wrapped by a shared pointer when used
    // A factory is used to construct them and handle hash caching
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
            /** A protected constructor to disallow public creation
             *  This must have take in the same arguments types as the hash function, minus the
             * hash These arguments may be taken in via copy, reference or move; ownership is given
             */
            Bool(const Hash h, const Op::Operation o);

            /** The hash function of this AST
             *  This must have take in the same arguments as the constructor, minus the hash
             *  These arguments args must be const values or references; this function must be pure
             */
            static Hash hash(const Op::Operation o);
        };

    } // namespace RawTypes

} // namespace AST

#endif
