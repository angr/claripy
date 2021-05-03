/**
 * @file
 * @brief This file defines Expression factory functions
 */
#ifndef __EXPRESSION_FACTORY_HPP__
#define __EXPRESSION_FACTORY_HPP__

#include "base.hpp"

#include "../hash.hpp"
#include "../utils.hpp"


namespace Expression {

    /** A factory used to construct Expression subclasses
     *  Arguments are passed by non-const forwarding reference
     *  @todo update eager_backends functionality
     */
    template <typename T, typename... Args> inline BasePtr factory(Args &&...args) {
        static_assert(Utils::is_ancestor<Base, T>, "T must derive from Expression::Base");
        return ::Factory::factory<Base, T>(std::forward<Args>(args)...);
    }

    /** Retrun true if the given hash is in the cache; and thus the assoicated object is alive
     *  Warning: by the time this function ends, the object may have died.
     */
    inline bool in_cache(const Hash::Hash h) { return ::Factory::in_cache<Base>(h); }

} // namespace Expression

#endif
