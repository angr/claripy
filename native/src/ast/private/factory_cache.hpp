/**
 * @file
 * @brief This file declares the AST factory cache
 */
#ifndef __AST_PRIVATE_FACTORYCACHE_HPP__
#define __AST_PRIVATE_FACTORYCACHE_HPP__

#include "cache.hpp"

#include "../constants.hpp"


namespace AST {

    // Forward declarations
    namespace RawTypes {
        class Base;
    }

    // The following should not be used outside of the ast directory
    namespace Private {

        /** Define a cache the AST factory can use */
        extern Private::Cache<::AST::Hash, RawTypes::Base> factory_cache;

    } // namespace Private

} // namespace AST

#endif
