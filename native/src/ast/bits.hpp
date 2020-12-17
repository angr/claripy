/**
 * @file
 * @brief This file defines the AST::Cached::Bits class and defines AST::Bits
 */
#ifndef __AST_BITS_HPP__
#define __AST_BITS_HPP__

#include "base.hpp"


/** A namespace used for the ast directory */
namespace AST {

    /** A namespace to denote self-caching classes
     *  These classes are unlikely to be accessed directly, but rather should be accessed via a
     * shared_ptr
     */
    namespace Cached {

        /** This class represents an AST of bits */
        class Bits : public Base {
          public:
            /** Virtual destructor */
            virtual ~Bits();

            /* def make_like(self, op, args, **kwargs): */
            /*     if 'length' not in kwargs: kwargs['length'] = self.length */
            /*     return Base.make_like(self, op, args, **kwargs) */

            /** Return the name of the type this class represents */
            std::string type_name() const;

            /** Return the name of the type this class represents irrespective of length */
            virtual std::string fundamental_type_name() const;

            /** The number of bits being represented */
            const Constants::Int length;

          protected:
            /** A protected constructor to disallow public creation
             *  This must have take in the same arguments as the hash function, minus the hash
             * which must be the first argument passed
             */
            Bits(const Hash h, const Ops::Operation o, const Constants::Int length);

          private:
            /** Delete all default constructors */
            DELETE_DEFAULTS(Bits)

            /** The hash function of this AST
             *  This must have take in the same arguments as the constructor, minus the hash
             * @todo not exactly, args in the constructor can consume inputs
             */
            static Hash hash(const Ops::Operation o, const Constants::Int length);

            /** Throw an exception if old and new_ are not of the same length @todo static */
            void check_replaceability(const ::AST::Bits &old, const ::AST::Bits &new_);

            /** Allow factories friend access */
            template <class T, typename... Args>
            friend T factory(std::set<BackendID> &&eager_backends, Args &&...args);
        };
    } // namespace Cached

} // namespace AST

#endif
