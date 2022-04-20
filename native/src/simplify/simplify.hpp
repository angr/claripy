/**
 * @file
 * @brief Define the simplify and cache methods
 */
#ifndef R_SRC_SIMPLIFY_SIMPLIFY_HPP_
#define R_SRC_SIMPLIFY_SIMPLIFY_HPP_

#include "manager.hpp"


namespace Simplify {
    /** thread local Simplify Manager */
    extern thread_local Manager manager;

    /** Simplifies a given Expr */
    inline Expr::BasePtr simplify(const Expr::BasePtr &e) {
        return manager.simplify(e);
    }

    /** Cache a simplification result done outside of simplify()
     *  This will override any result previously stored by simplify
     **/
    inline void cache(const Hash::Hash h, const Expr::BasePtr &e) {
        return manager.cache(h, e);
    }

    static_assert(std::is_same_v<Func, decltype(simplify)>, "simplify of wrong type");
} // namespace Simplify

#endif
