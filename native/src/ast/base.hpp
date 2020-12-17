/**
 * @file
 * @brief This file defines the AST::Cached::Base class and defines AST::Base
 */
#ifndef __AST_BASE_HPP__
#define __AST_BASE_HPP__

#include "../annotations/base.hpp"
#include "../ops/operations_enum.hpp"
#include "using_declarations.hpp"

#include "../constants.hpp"
#include "../macros.hpp"

#include <list>
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
    using Hash = uint_fast64_t;

    /** Define a type to store backend IDs
     * @todo: Change this to something else as needed
     */
    using BackendID = Constants::Int;


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
          public:
            /** The public factory used to create a Base */
            virtual ::AST::Base factory(const Ops::Operation o);

            /** Returns a string representation of this */
            virtual std::string repr(const bool inner = false, const Constants::Int max_depth = -1,
                                     const bool explicit_length = false) const;

            /** Return the name of the type this class represents */
            virtual std::string type_name() const;

            /************************************************/
            /*                Representation                */
            /************************************************/

            /** The top level operation this AST represents */
            const Ops::Operation op;

            /** The hash of the AST */
            const Hash id;

            /** A flag saying whether or not this AST is symbolic */
            const bool symbolic;

            /** A measure of how simplified this AST is */
            const Simplify simplified;

            /** Children ASTs */
            const std::vector<const ::AST::Base> children;

            /** A set of backents that are known to be unable to handle this AST */
            const std::set<const BackendID> errored_backends;

            /** A set of annotations applied onto this AST */
            const std::set<const Annotation::Base> annotations;

          protected:
            /** A protected constructor to disallow public creation */
            Base(const Ops::Operation o, const Hash);

            /************************************************/
            /*                   Statics                    */
            /************************************************/

            /** The hash function of this AST */
            static Hash hash(const Ops::Operation o);

            /** A static cache used to allow bases to */
            static std::map<Hash, std::weak_ptr<Base>> hash_cache;

          private:
            /** Delete all default constructors */
            DELETE_DEFAULTS(Base)
        };
    } // namespace Cached

} // namespace AST

#endif
