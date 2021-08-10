/**
 * @file
 * @brief This file defines the base expression
 */
#ifndef R_BACKEND_BASE_HPP_
#define R_BACKEND_BASE_HPP_

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
        DEFINE_IMPLICITS_ALL_NOEXCEPT(Base);

        // Pure virtual functions

        /** Create a new thread local solver and return an opaque shared pointer to it
         *  When this opaque shared pointer dies, the solver may also die as well
         *  Warning: Do *not* share solvers between threads
         */
        [[nodiscard]] virtual std::shared_ptr<void> new_tls_solver() const = 0;

        /** Check to see if the solver is in a satisfiable state */
        virtual bool satisfiable(const std::shared_ptr<void> &solver) = 0;

        /** Check to see if the solver is in a satisfiable state
         *  Temporarily adds the extra constraints to the solver
         */
        virtual bool satisfiable(const std::shared_ptr<void> &solver,
                                 const std::set<Expression::BasePtr> &extra_constraints) = 0;

        /** Check to see if the sol is a solution to expr w.r.t the solver; neither may be nullptr
         *  extra_constraints may be modified
         */
        virtual bool solution(const Expression::BasePtr &expr, const Expression::BasePtr &sol,
                              std::shared_ptr<void> &solver,
                              std::set<Expression::BasePtr> &extra_constraints) = 0;

        /** Check to see if the sol is a solution to expr w.r.t the solver; neither may be nullptr
         */
        virtual bool solution(const Expression::BasePtr &expr, const Expression::BasePtr &sol,
                              std::shared_ptr<void> &solver) = 0;

        /** Backend name */
        [[nodiscard]] virtual const char *name() const noexcept = 0;

        /** Simplify the given expression
         *  expr may not be nullptr
         */
        virtual Expression::BasePtr simplify_raw(const Expression::RawPtr expr) = 0;

        /** Check whether the backend can handle the given expression
         *  expr may not be nullptr
         */
        virtual bool handles_raw(const Expression::RawPtr expr) = 0;

        /** Clear caches to decrease memory pressure
         *  Note: if overriding this, it is advised to call this function from the derived version
         */
        virtual inline void downsize() = 0;

        /** Clear persistent data caches
         *  These are caches that are not just for optimization.
         *  It is up to the user to ensure that this function is only called when safe to do so
         *  Warning: Do not use this function unless you understand what it does to the specific
         *  backend that has implemented it! It may clear vital persistent data from memory.
         */
        virtual void clear_persistent_data() = 0;

        /** Return true if expr is always true
         *  expr may not be nullptr
         */
        virtual bool is_true_raw(const Expression::RawPtr expr) = 0;

        /** Return true if expr is always false
         *  expr may not be nullptr
         */
        virtual bool is_false_raw(const Expression::RawPtr expr) = 0;

        // Concrete functions

        /** Return true if expr is always true
         *  expr may not be nullptr
         */
        inline bool is_true(const Expression::BasePtr &expr) { return is_true_raw(expr.get()); }

        /** Return true if expr is always false
         *  expr may not be nullptr
         */
        inline bool is_false(const Expression::BasePtr &expr) { return is_false_raw(expr.get()); }

        /** Check whether the backend can handle the given expression
         *  expr may not be nullptr
         */
        inline bool handles(const Expression::BasePtr &expr) { return handles_raw(expr.get()); }

        /** Simplify the given expression
         *  expr may not be nullptr
         */
        inline Expression::BasePtr simplify(const Expression::BasePtr &expr) {
            return simplify_raw(expr.get());
        }

      protected:
        /** Default destructor */
        virtual ~Base() noexcept = default;
    };

} // namespace Backend

#endif
