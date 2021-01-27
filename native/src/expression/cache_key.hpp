/**
 * @file
 * @brief This file defines the Expression::CacheKey class
 * @todo This class may not be needed in the C++ version
 */
#ifndef __EXPRESSION_CACHE_KEY_HPP__
#define __EXPRESSION_CACHE_KEY_HPP__

#include "../macros.hpp"

#include <string>


namespace Expression {

    // Forward declarations
    namespace Raw::Type {
        class Base;
    }

    /** CacheKey is a reference to an Expression
     *  Two CacheKeys are considered equal when their hashes are equal
     */
    class CacheKey final {
      public:
        /** Constructor */
        CacheKey(const Raw::Type::Base &a);

        /** Returns a string representation of this */
        std::string repr() const;

        /** ExpressionCacheKey equality operator
         *  Two values are equal if their Expression's hashes are
         */
        bool operator==(const CacheKey &) const;

      private:
        /************************************************/
        /*                Representation                */
        /************************************************/

        /** The Expression this object refers to */
        const Raw::Type::Base &ref;
    };

} // namespace Expression

#endif
