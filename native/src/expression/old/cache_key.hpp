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
    class Base;

    /** CacheKey is a reference to an Expression
     *  Two CacheKeys are considered equal when their hashes are equal
     */
    class CacheKey final {
      public:
        /** Constructor */
        explicit inline CacheKey(const Raw::Type::Base &a) : ref { a } {}

        /** Returns a string representation of this */
        inline std::string repr() const noexcept { return std::to_string(this->ref.hash); }

      private:
        /************************************************/
        /*                Representation                */
        /************************************************/

        /** The Expression this object refers to */
        const Base &ref;

        /** Permit equality operator friend access */
        friend bool operator==(const CacheKey &, const CacheKey &);
    };

    /** ExpressionCacheKey equality operator
     *  Two values are equal if their Expression's hashes are
     */
    bool operator==(const CacheKey &, const CacheKey &);

} // namespace Expression

#endif
