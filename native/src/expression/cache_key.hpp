/**
 * @file
 * @brief This file defines the AST::CacheKey class
 * @todo This class may not be needed in the C++ version
 */
#ifndef __AST_CACHE_KEY_HPP__
#define __AST_CACHE_KEY_HPP__

#include "../macros.hpp"

#include <string>


namespace AST {

    // Forward declarations
    namespace RawTypes {
        class Base;
    }

    /** CacheKey is a reference to an AST
     *  Two CacheKeys are considered equal when their hashes are equal
     */
    class CacheKey {
      public:
        /** Constructor */
        CacheKey(const RawTypes::Base &a);

        /** Returns a string representation of this */
        std::string repr() const;

        /** ASTCacheKey equality operator
         *  Two values are equal if their AST's hashes are
         */
        bool operator==(const CacheKey &) const;

      private:
        /** Delete all default constructors */
        DELETE_DEFAULTS(CacheKey);

        /************************************************/
        /*                Representation                */
        /************************************************/

        /** The AST this object refers to */
        const RawTypes::Base &ref;
    };

} // namespace AST

#endif
