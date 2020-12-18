/**
 * @file
 * @brief This file defines the AST::RawTypes::Bits class and defines AST::Bits
 */
#ifndef __AST_BITS_HPP__
#define __AST_BITS_HPP__

#include "base.hpp"


/** A namespace used for the ast directory */
namespace AST {

    /** A namespace which contains the raw AST types that are constructed via AST::factory
     *  These classes are unlikely to be accessed directly, but rather should be via a shared_ptr
     */
    namespace RawTypes {

        /** This class represents an AST of bits */
        class Bits : public Base {
          public:
            /** Virtual destructor */
            virtual ~Bits();

            /** Return the name of the type this class represents */
            std::string type_name() const;

            /** Return the name of the type this class represents irrespective of length */
            virtual std::string fundamental_type_name() const;

            /** The number of bits being represented */
            const Constants::Int length;

          protected:
            /** A protected constructor to disallow public creation
             *  This must have take in the same arguments as the hash function, minus the hash
             *  which must be the first argument passed
             */
            Bits(const Hash h, const Ops::Operation o, const Constants::Int length);

          private:
            /** Delete all default constructors */
            DELETE_DEFAULTS(Bits)

            /** The hash function of this AST
             *  This must have take in the same arguments as the constructor, minus the hash
             *  @todo not exactly, args in the constructor can consume inputs
             */
            static Hash hash(const Ops::Operation o, const Constants::Int length);

            /** Throw an exception if old and new_ are not of the same length @todo static */
            void check_replaceability(const ::AST::Bits &old, const ::AST::Bits &new_);

            /** Allow factories friend access */
            template <typename T, typename... Args>
            friend T factory(std::set<BackendID> &&eager_backends, Args &&...args);

            /** Allow cache friend access
             *  We expose the constructor so that the cache may emplace new objects, which is
             *  faster than copying them in
             */
            friend class ::AST::Private::Cache<Hash, Base>;
        };
    } // namespace RawTypes

} // namespace AST

#endif
