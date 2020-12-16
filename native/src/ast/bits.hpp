/**
 * @file
 * @brief This file defines the AST::Cached::Bits class and defines AST::Bits
 */
#ifndef __AST_BITS_HPP__
#define __AST_BITS_HPP__

#include "../constants.hpp"

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
            /** Public constructor */
            Bits(const Ops::Operation o, const Hash, const Constants::Int length);

            /* def make_like(self, op, args, **kwargs): */
            /*     if 'length' not in kwargs: kwargs['length'] = self.length */
            /*     return Base.make_like(self, op, args, **kwargs) */

            /** Return the number of btis this AST represents */
            Constants::Int size() const;

            /** Return the name of the type this class represents */
            virtual std::string type_name() const;

          protected:
            /** The number of bits being represented */
            const Constants::Int length;

          private:
            /** Throw an exception if old and new_ are not of the same length @todo static */
            void check_replaceability(const ::AST::Bits &old, const ::AST::Bits &new_);
        };
    } // namespace Cached

    /** An abbreviation for a shared pointer to the cached bits class */
    using Bits = std::shared_ptr<Cached::Bits>;

} // namespace AST

#endif
