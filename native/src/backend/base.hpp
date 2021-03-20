/**
 * @file
 * @brief This file defines the base expression
 */
#ifndef __BACKEND_BASE_HPP__
#define __BACKEND_BASE_HPP__

#include "../expression.hpp"

#include <memory>
#include <vector>


namespace Backend {

    /** A SolverID type */
    using SolverID = Constants::UInt;

    /** The base Backend type
     *  All backends must subclass this
     */
    class Base {
      public:
        // Define implicits
        SET_IMPLICITS(Base, default)

        /** Default destructor */
        virtual ~Base() = default;

        // Pure virtual functions

        /** Check whether the backend can handle the given expression */
        virtual bool handles(const Expression::BasePtr &expr) = 0;

        /** Simplify the given expression */
        virtual Expression::BasePtr simplify(const Expression::BasePtr &expr) = 0;

        /** Backend name */
        virtual Constants::CCSC name() const = 0;

        // Virtual functions

        /** Clear caches to decrease memory pressure
         *  Note: if overriding this, it is advised to call this function from the derived version
         */
        virtual inline void downsize() {
            is_true_cache.unique().first.clear();
            is_false_cache.unique().first.clear();
        }

        // Non-virtual functions

        /** Create a new thread local solver and return its id
         *  This ID must be unique across all solvers of backends of the current thread
         *  Warning: Do *not* share SolverIDs between threads, this is undefined behavior
         */
        SolverID new_tls_solver() {
            static std::atomic<Constants::UInt> counter { 0 };
            auto id = ++counter;                            // atomic pre-increment
            auto new_solver { new_tls_solver_with_id(id) }; // should be inlined by compiler
            solvers.emplace(id, std::move(new_solver));
            return id;
        }

#if 0
        // true / false ones here
		template <bool B> bool is_B
			// Since B is a constant there should be no runtime overhead here
			is_b_cache = B ? ( is_true_cache : is_false_cache );
			is_not_b_cache = (!B) ? ( is_true_cache : is_false_cache );
			//
#endif

      protected:
        /** Create a new thread local solver and return a shared pointer to it
         *  Note: we return a shared_ptr<void> to keep things abstract
         *  Functions which later access the solver map must properly cast this
         */
        std::shared_ptr<void> new_tls_solver_with_id(const SolverID id) = 0;

        /** Clears the given thread-safe cache */
        template <typename Cache>
        static void thread_safe_clear_cache(Utils::ThreadSafe::Mutable &cache) {
            cache.unique().first.clear();
        }

        // Types

        /** A weak pointer to the expression base type */
        using WPtr = std::weak_ptr<Utils::InternalType<Expression::BasePtr>>;

        /** A weak pointer map that fundamentally maps Expressions to values
         *  weak_pointers cannot be map keys so we use the hash as a key instead
         */
        template <typename T>
        using WeakExpressionMap = std::map<Hash::Hash, const std::pair<WPtr, T>>;

        // Non-constant variables

        /** A map from SolverIDs to a shared pointers of any type
         *  In this case, the pointers to the solvers must dynamic casted before use
         */
        static thread_local Utils::ThreadSafe::Mutable<std::map<SolverID, std::shared_ptr<void>>>
            solvers;

        // Caches

        /** is_true cache
         *  Map an expression hash to the result of is_true and to a weak pointer
         *  that points to the expression that has the key as a hash value
         */
        static Utils::ThreadSafe::Mutable<WeakExpressionMap<bool>> is_true_cache;

        /** is_false cache
         *  Map an expression hash to the result of is_false and to a weak pointer
         *  that points to the expression that has the key as a hash value
         */
        static Utils::ThreadSafe::Mutable<WeakExpressionMap<bool>> is_false_cache;
    };

} // namespace Backend

#endif
