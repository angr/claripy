/**
 * @file
 * @brief This file defines the AST::RawTypes::Bits class and defines AST::Bits
 */
#ifndef __AST_RAWTYPES_BITS_HPP__
#define __AST_RAWTYPES_BITS_HPP__

#include "base.hpp"


namespace AST {

    // These types should be wrapped by a shared pointer when used
    // A factory is used to construct them and handle hash caching
    namespace RawTypes {

        /** This class represents an AST of bits */
        class Bits : public Base {
            AST_RAWTYPES_INIT_AST_BASE_SUBCLASS(Bits)
          public:
            AST_RAWTYPES_DECLARE_AST_SUBBITS_TYPENAME

            /** Virtual destructor */
            virtual ~Bits();

            /** The number of bits being represented */
            const Constants::Int length;

          protected:
            /** A protected constructor to disallow public creation
             *  This must have take in the same arguments types as the hash function, minus the
             * hash These arguments may be taken in via copy, reference or move; ownership is given
             */
            Bits(const Hash h, const Ops::Operation o, const Constants::Int length);

          private:
            /** The hash function of this AST
             *  This must have take in the same arguments as the constructor, minus the hash
             *  These arguments args must be const values or references; this function must be pure
             */
            static Hash hash(const Ops::Operation o, const Constants::Int length);

            /** Throw an exception if old and new_ are not of the same length @todo static */
            void check_replaceability(const ::AST::Bits &old, const ::AST::Bits &new_);
        };

    } // namespace RawTypes

} // namespace AST

#endif
