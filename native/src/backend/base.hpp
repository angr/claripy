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

    /** A Solver type */
    using Solver = std::shared_ptr<void>;

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

        /** Simplify the given expression */
        virtual Expression::BasePtr simplify(const Expression::RawPtr expr) = 0;

        /** Backend name */
        [[nodiscard]] virtual Constants::CCSC name() const noexcept = 0;

        /** Return true if expr is always true */
        virtual bool is_true(const Expression::RawPtr &expr, const Solver &solver,
                             const std::vector<Expression::BasePtr> extra_constraints = {}) = 0;

        /** Return true if expr is always false */
        virtual bool is_false(const Expression::RawPtr &expr, const Solver &solver,
                              const std::vector<Expression::BasePtr> extra_constraints = {}) = 0;

        /** Check whether the backend can handle the given expression */
        virtual bool handles(const Expression::RawPtr expr) = 0;

        /** Create a new thread local solver and return an opaque shared pointer to it
         *  When this opaque shared pointer dies, the solver may also die as well
         *  Warning: Do *not* share solvers between threads
         */
        [[nodiscard]] virtual std::shared_ptr<void> new_tls_solver() const = 0;

        // Virtual functions

        /** Clear caches to decrease memory pressure
         *  Note: if overriding this, it is advised to call this function from the derived version
         */
        virtual inline void downsize() {
            is_true_cache.unique().first.clear();
            is_false_cache.unique().first.clear();
        }

      protected:
        // Caches

        /** is_true cache
         *  Map an expression hash to the result of is_true
         */
        static Utils::ThreadSafe::Mutable<std::map<Hash::Hash, const bool>> is_true_cache;

        /** is_false cache
         *  Map an expression hash to the result of is_false
         */
        static Utils::ThreadSafe::Mutable<std::map<Hash::Hash, const bool>> is_false_cache;
    };

} // namespace Backend

#endif
