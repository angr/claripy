/**
 * @file base.hpp
 * @brief This file defines the AST::Base class
 */
#ifndef __AST_BASE_HPP__
#define __AST_BASE_HPP__

#include "../annotations/base.hpp"
#include "../ops/operations_enum.hpp"

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
        /** A factory used to construct Base's
         * If an AST with the same hash already exists, it returns that AST. Otherwise it
         * constructs a new AST
         * @param op:            The AST operation ('__add__', 'Or', etc)
         * @param args:          The arguments to the AST operation (i.e., the objects to add)
         * @param variables:     The symbolic variables present in the AST (default: empty set)
         * @param symbolic:      A flag saying whether or not the AST is symbolic (default: False)
         * @param length:        An integer specifying the length of this AST (default: None)
         * @param simplified:    A measure of how simplified this AST is. 0 means unsimplified,
         *						   1 means fast-simplified (basically, just
         *undoing the Reverse op), and 2 means simplified through z3.
         * @param errored:        A set of backends that are known to be unable to handle this AST.
         * @param eager_backends: A list of backends with which to attempt eager evaluation
         * @param annotations:    A frozenset of annotations applied onto this AST.
         */
        static std::shared_ptr<Base>
        factory(const Ops::Operations op, const std::vector<Base> args,
                const std::vector<std::string> &variables, const bool symbolic, const Int length,
                const Simplify simplified, const std::set<BackendID> errored,
                const std::vector<BackendID> eager_backends,
                const std::set<Annotation::Base> annotations);

      protected:
        /** A protected constructor to disallow public creation */
        Base();

        /** Returns a string representation of this */
        virtual std::string repr(const bool inner = false, const Int max_depth = -1,
                                 const bool explicit_length = false) const;

        /** Return the name of the type this class represents */
        virtual std::string type_name() const;

        // Representation
        /** The hash of the AST */
        const Hash hash;

        /** A static cache used to allow bases to */
        static std::map<Hash, std::weak_ptr<Base>> hash_cache;

      private:
        // Friends
        /** Allow CacheKey friend-access */
        friend class CacheKey;
    };

} // namespace AST

#endif
