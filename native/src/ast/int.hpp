/**
 * @file
 * @brief This file defines the AST::Cached::Int class and defines AST::Int
 */
#ifndef __AST_INT_HPP__
#define __AST_INT_HPP__

#include "../macros.hpp"

#include "base.hpp"


/** A namespace used for the ast directory */
namespace AST {

    /** A namespace to denote self-caching classes
     *  These classes are unlikely to be accessed directly, but rather should be accessed via a
     * shared_ptr
     */
    namespace Cached {

        /** An AST representing an integer */
        class Int : public Base {

            /** Return the name of the type this class represents */
            std::string type_name() const;

            /** A private constructor to disallow public creation
             *  This must have take in the same arguments as the hash function, minus the hash
             *  which must be the first argument passed
             */
            Int(const Hash h, const Ops::Operation o);

            /** Delete all default constructors */
            DELETE_DEFAULTS(Int)

            /** The hash function of this AST
             *  This must have take in the same arguments as the constructor, minus the hash
             * @todo not exactly, args in the constructor can consume inputs
             */
            static Hash hash(const Ops::Operation o, const Constants::Int length);

            /** Allow factories friend access */
            template <class T, typename... Args>
            friend T factory(std::set<const BackendID> &&eager_backends, Args &&...args);
        };

    } // namespace Cached

} // namespace AST

#endif
