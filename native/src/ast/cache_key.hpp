/**
 * @file cache_key.hpp
 * @brief This file defines the AST::CacheKey class
 * @todo This class may not be needed in the C++ version
 */
#ifndef __AST_CACHE_KEY_HPP__
#define __AST_CACHE_KEY_HPP__

#include <string>

#include <stdio.h>


/** A namespace used for the ast directory */
namespace AST {

    // Forward declarations
    class Base;


    /** CacheKey is a reference to an AST
     *  Two CacheKeys are considered equal when their hashes are equal
     */
    class CacheKey {
      public:
        /** Constructor */
        CacheKey(const Base &a);
        /** Returns a string representation of this */
        char *repr() const;

      private:
        // Representation
        /** The AST this object refers to */
        const Base &ref;
    };

    /** ASTCacheKey equality operator
     *  Two values are equal if their AST
     */
    bool operator==(const CacheKey &a, const CacheKey &b);

} // namespace AST

#endif
