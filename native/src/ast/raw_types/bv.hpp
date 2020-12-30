/**
 * @file
 * Boolbrief This file defines the AST::RawTypes::BV class and defines AST::BV
 */
#ifndef __AST_RAWTYPES_BV_HPP__
#define __AST_RAWTYPES_BV_HPP__

#include "bits.hpp"


namespace AST {

    // These types should be wrapped by a shared pointer when used
    // A factory is used to construct them and handle hash caching
    namespace RawTypes {

        /** This class represents an AST bit vector */
        class BV : public Bits {
            AST_RAWTYPES_INIT_AST_BITS_SUBCLASS(BV)

            /** A protected constructor to disallow public creation
             *  This must have take in the same arguments types as the hash function, minus the
             * hash These arguments may be taken in via copy, reference or move; ownership is given
             */
            BV(const Hash h, const Op::Operation o);

            /** The hash function of this AST
             *  This must have take in the same arguments as the constructor, minus the hash
             *  These arguments args must be const values or references; this function must be pure
             */
            static Hash hash(const Op::Operation o);
        };

    } // namespace RawTypes

} // namespace AST

#endif
