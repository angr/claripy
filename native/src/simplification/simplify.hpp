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
        inline Expression::BasePtr simplify(const Expression::BasePtr &old) {
            UTILS_AFFIRM_NOT_NULL_DEBUG(old->op); // Sanity check
            if (const auto itr { op_map.find(old->op->cuid) }; itr != op_map.end()) {
                return itr->second(old);
            }
            else {
                Utils::Log::verbose(
                    "Simplify found no suitable claricpp simplifier for the given expression");
                return old;
            }
        }
    } // namespace Private

    /** Simplify old and return the result
     *  old may not be nullptr
     */
    inline Expression::BasePtr simplify(const Expression::BasePtr &old) {
        UTILS_AFFIRM_NOT_NULL_DEBUG(old);
        if (auto lookup { Private::cache.find(old->hash) }; lookup) {
            Utils::Log::verbose("Simplification cache hit");
            return lookup;
        }
        auto ret { Private::simplify(old) };
        cache(old->hash, ret);
        return ret;
    }
} // namespace Simplification

#endif
