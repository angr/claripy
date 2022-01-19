/**
 * @file
 * @brief Define the simplification manager class
 */
#ifndef R_SIMPLIFY_MANAGER_HPP_
#define R_SIMPLIFY_MANAGER_HPP_

#include "constants.hpp"

#include "../op.hpp"


namespace Simplify {

    /** Simplification Manager
     *  Do *not* share this between threads
     */
    class Manager {
      public:
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

        // Adders

        /** Add a simplifier function to use on Exprs of the given op cuid */
        inline void register_(const CUID::CUID cuid, CTSC<Func> func) {
            {
                auto [m, lock] { map.scoped_unique() };
                add_to_vec(m[cuid], func);
            }
            Util::Log::debug<SimplifyLog>("Simplify::Manager registered new op simplifier");
        }

        /** Add a simplifier function to use on all Exprs */
        inline void register_(CTSC<Func> func) {
            {
                auto [v, lock] { vec.scoped_unique() };
                add_to_vec(v, func);
            }
            Util::Log::info<SimplifyLog>("Simplify::Manager registered new global simplifier");
        }

      private:
        /** Simplify old and return the result
         *  old may not be nullptr
         */
        inline Expr::BasePtr no_cache_simplify(const Expr::BasePtr &old) {
            UTIL_ASSERT_NOT_NULL_DEBUG(old->op); // Sanity check
            Expr::BasePtr ret { old };
            // Op map
            {
                auto [m, lock] = map.scoped_shared();
                if (const auto itr { m.find(old->op->cuid) }; itr != m.end()) {
                    for (const auto &f : itr->second) {
                        ret = f(ret);
                    }
                }
            }
            // Base vector
            {
                auto [v, lock] = vec.scoped_shared();
                for (const auto &f : v) {
                    ret = f(ret);
                }
            }
            return ret;
        }

        /** Add a simplifier function to the vector */
        static inline void add_to_vec(Vec &v, CTSC<Func> f) {
            for (const auto i : v) {
                UTIL_ASSERT(Util::Err::Python::Runtime, i != f,
                            "Given simplifier already in op_map");
            }
            v.emplace_back(f);
        }

        // Representation

        /** The simplification cache */
        Util::WeakCache<Hash::Hash, Expr::Base> wcache {};

        /** Simplifiers that run on all ops */
        static Util::ThreadSafe::Mutable<Vec> vec;
        /** Determines which functions to run on which ops */
        static Util::ThreadSafe::Mutable<Map> map;
    };

} // namespace Simplify

#endif