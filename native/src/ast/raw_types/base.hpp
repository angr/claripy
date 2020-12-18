/**
 * @file
 * @brief This file defines the AST::RawTypes::Base class and defines AST::Base
 */
#ifndef __AST_BASE_HPP__
#define __AST_BASE_HPP__

#include "../../annotations/base.hpp"
#include "../../macros.hpp"
#include "../../ops/operations_enum.hpp"
#include "../constants.hpp"
#include "../using_declarations.hpp"

#include <list>
#include <map>
#include <memory>
#include <set>
#include <string>
#include <vector>


/** A namespace used for the ast directory */
namespace AST {

    // Forward declarations
    class CacheKey;
    namespace Private {
        template <typename A, typename B> class Cache;
    }

    /** A type-safe simplify-level enumeration */
    enum class Simplify { UN, FULL, LITE };

    /** A type-safe repr-level enumeration */
    enum class Repr { LITE, MID, FULL };

    /** A namespace which contains self-caching classes and things related to AST caching
     *  These classes are unlikely to be accessed directly, but rather should be accessed via a
     * shared_ptr
     */
    namespace RawTypes {

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
            /** Virtual destructor */
            virtual ~Base();

            /** Returns a string representation of this */
            virtual std::string repr(const bool inner = false, const Constants::Int max_depth = -1,
                                     const bool explicit_length = false) const;

            /** Return the name of the type this class represents */
            virtual std::string type_name() const;

            /************************************************/
            /*                Representation                */
            /************************************************/

            /** The hash of the AST
             *  This variable is intentionally declared first as we want it to be the first
             * argument passed to the Base() constructor; since it was declared first most
             * compilers will issue a warning if it is not set before all other member variables */
            const Hash id;

            /** The top level operation this AST represents */
            const Ops::Operation op;

#if 0
            /** A flag saying whether or not this AST is symbolic */
            const bool symbolic;

            /** A measure of how simplified this AST is */
            const Simplify simplified;

            /** Children ASTs */
            const std::vector<const ::AST::Base> children;

            /** A set of backents that are known to be unable to handle this AST */
            const std::set<BackendID> errored_backends;

            /** A set of annotations applied onto this AST */
            const std::set<const Annotation::Base> annotations;
#endif

          protected:
            /************************************************/
            /*                   Statics                    */
            /************************************************/

            /** The hash function of this AST
             *  This must have take in the same arguments as the constructor, minus the hash
             */
            static Hash hash(const Ops::Operation o);

            /************************************************/
            /*                 Constructors                 */
            /************************************************/

            /** A protected constructor to disallow public creation
             *  This must have take in the same arguments as the hash function, minus the hash
             * which must be the first argument passed
             */
            Base(const Hash h, const Ops::Operation o);

          private:
            /** Delete all default constructors */
            DELETE_DEFAULTS(Base)

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
