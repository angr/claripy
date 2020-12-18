/**
 * @file
 * @brief This file defines the AST::Cached::Bool class and defines AST::Bool
 */
#ifndef __AST_BOOL_HPP__
#define __AST_BOOL_HPP__

#include "base.hpp"


/** A namespace used for the ast directory */
namespace AST {

    /** A namespace which contains self-caching classes and things related to AST caching
     *  These classes are unlikely to be accessed directly, but rather should be accessed via a
     * shared_ptr
     */
    namespace Cached {

        /** This class represents an AST boolean */
        class Bool : public Base {
          public:
            /** Return true if the AST evaluates to true */
            bool is_true() const;

            /** Return true if the AST evaluates to false */
            bool is_false() const;

            /** Return the name of the type this class represents */
            std::string type_name() const;

          private:
            /** A private constructor to disallow public creation
             *  This must have take in the same arguments as the hash function, minus the hash
             *  which must be the first argument passed
             */
            Bool(const Hash h, const Ops::Operation o);

            /** Delete all default constructors */
            DELETE_DEFAULTS(Bool)

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
