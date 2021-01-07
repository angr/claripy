/**
 * @file
 * @brief This file declares the Expression factory cache
 */
#ifndef __EXPRESSION_PRIVATE_FACTORYCACHE_HPP__
#define __EXPRESSION_PRIVATE_FACTORYCACHE_HPP__

#include "cache.hpp"

#include "../constants.hpp"


namespace Expression {

    // Forward declarations
    namespace Raw::Type {
        class Base;
    }

    // The following should not be used outside of the ast directory
    namespace Private {

        /** Define a cache the Expression factory can use */
        extern Private::Cache<::Expression::Hash, Raw::Type::Base> factory_cache;

    } // namespace Private

} // namespace Expression

#endif
