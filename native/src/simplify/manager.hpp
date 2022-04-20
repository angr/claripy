/**
 * @file
 * @brief Define the simplification manager class
 */
#ifndef R_SRC_SIMPLIFY_MANAGER_HPP_
#define R_SRC_SIMPLIFY_MANAGER_HPP_

#include "constants.hpp"
#include "simplifiers.hpp"

#include "../op.hpp"


namespace Simplify {

    /** Simplification Manager
     *  Do *not* share this between threads
     */
    class Manager {
      public:
        /** Constructor */
        inline Manager() : vec { builtin_vec() }, map { builtin_map() } {}

        /** Simplify old and return the result
         *  old may not be nullptr
         *  Note: Calls simplifiers in op_map first in order of the vector, then the base vector
         */
        inline Expr::BasePtr simplify(const Expr::BasePtr &old) {
            UTIL_ASSERT_NOT_NULL_DEBUG(old);
            if (auto lookup { wcache.find(old->hash) }; lookup) {
                Util::Log::verbose("Simplification cache hit");
                return lookup;
            }
            auto ret { no_cache_simplify(old) };
            cache(old->hash, ret);
            return ret; // Recurse until fully simplified
        }

        /** A method for adding to the simplification cache
         *  Record that an Expr with Hash h simplifies to non-null Expr pointer e
         *  This will override any result previously stored by simplify
         */
        inline void cache(const Hash::Hash h, const Expr::BasePtr &e) {
            UTIL_ASSERT_NOT_NULL_DEBUG(e);
            wcache.put(h, e);
        }

        /** A nullptr_t override which is noexcept */
        inline void set_python_simplifier(std::nullptr_t) noexcept {
            Util::Log::info<SimplifyLog>("Simplify::Manager cleared python simplifier");
            py_simp = nullptr; // nullptr_t uses specialization that is noexcept
        }

        /** Add a simplifier function to use on Exprs of the given op cuid
         *  Null functions are permitted but nullptr will be sent to a noexcept override
         */
        inline void set_python_simplifier(const std::function<Func> &func) {
            Util::Log::info<SimplifyLog>("Simplify::Manager set python simplifier");
            py_simp = func;
        }

      private:
        /** Simplify old and return the result
         *  old may not be nullptr
         */
        inline Expr::BasePtr no_cache_simplify(const Expr::BasePtr &old) {
            UTIL_ASSERT_NOT_NULL_DEBUG(old->op); // Sanity check
            Expr::BasePtr ret { old };
            // Op map
            if (const auto itr { map.find(old->op->cuid) }; itr != map.end()) {
                for (const auto &f : itr->second) {
                    ret = f(ret);
                }
            }
            // Base vector
            for (const auto &f : vec) {
                ret = f(ret);
            }
            // Python simplifier
            if (UNLIKELY(py_simp)) {
                ret = py_simp(ret);
            }
            return ret;
        }

        // Representation

        /** The simplification cache */
        Util::WeakCache<Hash::Hash, Expr::Base> wcache {};

        /** Simplifiers that run on all ops */
        const Vec vec;
        /** Determines which functions to run on which ops */
        const Map map;

        /** Python simplifier */
        std::function<Func> py_simp { nullptr };
    };

} // namespace Simplify

#endif