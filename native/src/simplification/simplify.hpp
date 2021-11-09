/**
 * @file
 * @brief Define the simplify method
 */
#ifndef R_SIMPLIFICATION_SIMPLIFY_HPP_
#define R_SIMPLIFICATION_SIMPLIFY_HPP_

#include "cache.hpp"
#include "op_map.hpp"


namespace Simplification {

    namespace Private {
        /** Simplify old and return the result
         *  old may not be nullptr
         */
        inline Expr::BasePtr simplify(const Expr::BasePtr &old) {
            UTIL_AFFIRM_NOT_NULL_DEBUG(old->op); // Sanity check
            if (const auto itr { op_map.find(old->op->cuid) }; itr != op_map.end()) {
                return itr->second(old);
            }
            else {
                Util::Log::verbose(
                    "Simplify found no suitable claricpp simplifier for the given expr");
                return old;
            }
        }
    } // namespace Private

    /** Simplify old and return the result
     *  old may not be nullptr
     */
    inline Expr::BasePtr simplify(const Expr::BasePtr &old) {
        UTIL_AFFIRM_NOT_NULL_DEBUG(old);
        if (auto lookup { Private::cache.find(old->hash) }; lookup) {
            Util::Log::verbose("Simplification cache hit");
            return lookup;
        }
        auto ret { Private::simplify(old) };
        cache(old->hash, ret);
        return ret;
    }
} // namespace Simplification

#endif
