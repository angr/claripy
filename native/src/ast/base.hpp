/**
 * @file base.hpp
 * @brief This file defines the AST::Cached::Base class and define AST::Base
 */
#ifndef __AST_BASE_HPP__
#define __AST_BASE_HPP__

#include "../annotations/base.hpp"
#include "../ops/operations_enum.hpp"
#include "using_declarations.hpp"

#include "../constants.hpp"

#include <map>
#include <memory>
#include <set>
#include <string>
#include <vector>


/** A namespace used for the ast directory */
namespace AST {

    /** Define a type to store hashes
     * @todo: Change this to something else as needed
     */
    using Hash = std::string;

    /** Define a type to store backend IDs
     * @todo: Change this to something else as needed
     */
    using BackendID = Int;


    // Forward declarations
    class CacheKey;

    /** A type-safe simplify-level enumeration */
    enum class Simplify { UN, FULL, LITE };

    /** A type-safe repr-level enumeration */
    enum class Repr { LITE, MID, FULL };

    /** A namespace to denote self-caching classes
     *  These classes are unlikely to be accessed directly, but rather should be accessed via a
     * shared_ptr
     */
    namespace Cached {

        /** This is the base class of all claripy ASTs.
         * An AST tracks a tree of operations on arguments.
         * This class should not be instanciated directly - instead, use one of the
         * constructor functions (BVS, BVV, FPS, FPV...) to construct a leaf node and then
         * build more complicated expressions using operations. AST objects have *hash
         * identity*. This means that an AST that has the same hash as another AST will be the
         * *same* object. This is critical for efficient memory usage. As an example, the
         * following is true:: a, b = two different ASTs c = b + a d = b + a assert c is d
         */
        class Base {
          protected:
            /** A protected constructor to disallow public creation */
            Base(const Ops::Operation o, const Hash);

            /** Returns a string representation of this */
            virtual std::string repr(const bool inner = false, const Int max_depth = -1,
                                     const bool explicit_length = false) const;

            /** Return the name of the type this class represents */
            virtual std::string type_name() const;

            /************************************************/
            /*                   Statics                    */
            /************************************************/

            /** A static cache used to allow bases to */
            static std::map<Hash, std::weak_ptr<Base>> hash_cache;

            /************************************************/
            /*                Representation                */
            /************************************************/

            /** The top level operation this AST represents */
            const Ops::Operation op;

            /** The hash of the AST */
            const Hash hash;

            /************************************************/
            /*                   Friends                    */
            /************************************************/

            /** Allow CacheKey friend-access */
            friend class AST::CacheKey;
        };
    } // namespace Cached

} // namespace AST

#endif
