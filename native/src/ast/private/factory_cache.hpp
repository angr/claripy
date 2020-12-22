/**
 * @file
 * @brief This file declares the AST factory cache
 */
#ifndef __AST_PRIVATE_FACTORYCACHE_HPP__
#define __AST_PRIVATE_FACTORYCACHE_HPP__

#include "cache.hpp"

#include "../constants.hpp"


/** A namespace used for the ast directory */
namespace AST {

    // Forward declarations
    namespace RawTypes {
        class Base;
    }

    /** A namespace used to designate certain items in ast as private
     *  These functions should not be called outside of the ast directory
     *  This is useful for helper functions templated functions call
     */
    namespace Private {

        /** Define a cache the AST factory can use */
        extern Private::Cache<::AST::Hash, RawTypes::Base> factory_cache;

    } // namespace Private

} // namespace AST

#endif
