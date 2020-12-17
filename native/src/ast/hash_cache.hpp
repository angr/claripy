/**
 * @file
 * @brief This file defines the AST hash cache
 */
#ifndef __AST_HASH_CACHE_HPP__
#define __AST_HASH_CACHE_HPP__

#include "constants.hpp"

#include <map>


/** A namespace used for the ast directory */
namespace AST {

    // Forward declarations
    namespace Cached {
        class Base;
    }

    /** A namespace used to designate certain items in ast as private
     *  These functions should not be called outside of the ast directory
     *  This is useful for helper functions templated functions call
     */
    namespace Private {

        /** A static cache used to allow bases to */
        std::map<Hash, std::weak_ptr<Cached::Base>> hash_cache;

    } // namespace Private

} // namespace AST

#endif
