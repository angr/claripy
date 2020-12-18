/**
 * @file
 * @brief This file defines the AST::Cached::String class and defines AST::String
 */
#ifndef __AST_STRING_HPP__
#define __AST_STRING_HPP__

#include "bits.hpp"


/** A namespace used for the ast directory */
namespace AST {

    /** A namespace which contains self-caching classes and things related to AST caching
     *  These classes are unlikely to be accessed directly, but rather should be accessed via a
     * shared_ptr
     */
    namespace Cached {

        /** An AST representing a string */
        class String : public Bits {

            /** Create a concrete String
             *  @todo kwargs
             */
            /* static ::AST::String Concrete(const std::string & value, const Constants::Int
             * length); */

            /** Return the name of the type this class represents irrespective of length */
            std::string fundamental_type_name() const;

            /** A private constructor to disallow public creation
             *  This must have take in the same arguments as the hash function, minus the hash
             *  which must be the first argument passed
             */
            String(const Hash h, const Ops::Operation o);

            /** Delete all default constructors */
            DELETE_DEFAULTS(String)

            /** The hash function of this AST
             *  This must have take in the same arguments as the constructor, minus the hash
             * @todo not exactly, args in the constructor can consume inputs
             */
            static Hash hash(const Ops::Operation o, const Constants::Int length);

            /** Allow factories friend access */
            template <typename T, typename... Args>
            friend T factory(std::set<BackendID> &&eager_backends, Args &&...args);

            /** Allow cache friend access
             *  We expose the constructor so that the cache may emplace new objects, which is
             *  faster than copying them in
             */
            friend class ::AST::Private::Cache<Hash, Base>;
        };

    } // namespace Cached

} // namespace AST

#endif
