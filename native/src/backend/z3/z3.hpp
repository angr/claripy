/**
 * @file
 * @brief This file defines the Z3 backend
 */
#ifndef R_BACKEND_Z3_Z3_HPP_
#define R_BACKEND_Z3_Z3_HPP_

#include "bool_tactic.hpp"
#include "dispatch.hpp"

#include "../../error.hpp"
#include "../generic.hpp"


namespace Backend::Z3 {

    /** The Z3 backend */
    class Z3 final : public Z3Super {
        static_assert(!use_apply_annotations, "Z3 objects do not support holding annotations");

      public:
        /********************************************************************/
        /*                     Small Function Overrides                     */
        /********************************************************************/

        /** Destructor */
        ~Z3() noexcept override = default;

        /** Clears translocation data */
        inline void clear_persistent_data() override final {
            symbol_annotation_translocation_data.clear();
        }

        /** The name of this backend */
        [[nodiscard]] inline const char *name() const noexcept override final { return "z3"; }

        /** Create a tls solver */
        [[nodiscard]] inline virtual std::shared_ptr<z3::solver> new_tls_solver() const {
            return std::make_shared<z3::solver>(Private::tl_ctx);
        }

        /** Check to see if the solver is in a satisfiable state */
        inline bool satisfiable(const std::shared_ptr<z3::solver> &solver) {
            return solver->check() == z3::check_result::sat;
            // @todo: model callback
        }

        /** Check to see if the solver is in a satisfiable state
         *  Temporarily adds the extra constraints to the solver
         */
        inline bool satisfiable(const std::shared_ptr<z3::solver> &solver,
                                const std::set<Expression::BasePtr> &extra_constraints) {
            // If extra constraints are empty, skip them
            if (extra_constraints.empty()) {
                return satisfiable(solver);
            }
            // Load each extra constraint into the solver
            UTILS_AFFIRM_NOT_NULL_DEBUG(solver);
            solver->push();
            for (const auto &i : extra_constraints) {
                const auto c { convert(i) };
                solver->add(c);
            }
            // Check if the solver is in a satisfiable state, then pop the extra constraints
            const bool ret { satisfiable(solver) };
            solver->pop();
            return ret;
        }

        /** Check to see if the sol is a solution to expr w.r.t the solver; neither may be nullptr
         *  extra_constraints may be modified
         */
        inline bool solution(const Expression::BasePtr &expr, const Expression::BasePtr &sol,
                             std::shared_ptr<z3::solver> &solver,
                             std::set<Expression::BasePtr> &extra_constraints) {
            extra_constraints.emplace(to_eq(expr, sol));
            return satisfiable(solver, extra_constraints);
        }

        /** Check to see if sol is a solution to expr w.r.t the solver; neither may be nullptr */
        inline bool solution(const Expression::BasePtr &expr, const Expression::BasePtr &sol,
                             std::shared_ptr<z3::solver> &solver) {
            static thread_local std::set<Expression::BasePtr> s;
            s.clear();
            return solution(expr, sol, solver, s);
        }

        /** The method used to simplify z3 boolean expressions */
        inline z3::expr bool_simplify(const z3::expr &expr) {
            static thread_local BoolTactic bt {};
            return bt(expr);
        }

        /** Simplify the given expression
         *  expr may not be nullptr
         */
        inline Expression::BasePtr simplify_raw(const Expression::RawPtr expr) override final {
            UTILS_AFFIRM_NOT_NULL_DEBUG(expr);
            namespace Ex = Expression;
            switch (expr->cuid) {
                case Ex::Bool::static_cuid: {
                    auto b_obj { convert(expr) };
                    b_obj = bool_simplify(b_obj);
                    return abstract(b_obj);
                }
                case Ex::BV::static_cuid: {
                    auto b_obj = convert(expr);
                    b_obj = b_obj.simplify();
                    return abstract(b_obj);
                }
                default: {
#ifdef DEBUG
                    auto ret { Ex::find(expr->hash) };
                    using Err = Utils::Error::Unexpected::HashCollision;
                    Utils::affirm<Err>(ret.get() == expr, WHOAMI_WITH_SOURCE);
                    return ret;
#else
                    return Ex::find(expr->hash);
#endif
                }
            }
        }

        /** This dynamic dispatcher converts expr into a backend object
         *  All arguments of expr that are not primitives have been
         *  pre-converted into backend objects and are in args
         *  Arguments must be popped off the args stack if used
         *  expr may not be nullptr
         *  Warning: This function may internally do unchecked static casting, we permit this
         *  *only* if the cuid of the expression is of or derive from the type being cast to.
         */
        inline z3::expr dispatch_conversion(const Expression::RawPtr expr,
                                            std::vector<const z3::expr *> &args) override final {
            return Private::dispatch_conversion(expr, args, symbol_annotation_translocation_data);
        }

        /** Abstract a backend object into a claricpp expression */
        inline AbstractionVariant
        dispatch_abstraction(const z3::expr &b_obj,
                             std::vector<AbstractionVariant> &args) override final {
            return Private::dispatch_abstraction(b_obj, args,
                                                 symbol_annotation_translocation_data);
        }

      private:
        /** Create a == b; neither may be nullptr */
        static Expression::BasePtr to_eq(const Expression::BasePtr &a,
                                         const Expression::BasePtr &b) {
            UTILS_AFFIRM_NOT_NULL_DEBUG(a);
            namespace Ex = Expression;
            switch (a->cuid) {
                case Ex::Bool::static_cuid:
                    return Create::eq<Ex::Bool>(a, b);
                case Ex::BV::static_cuid:
                    return Create::eq<Ex::BV>(a, b);
                case Ex::FP::static_cuid:
                    return Create::eq<Ex::FP>(a, b);
                case Ex::String::static_cuid:
                    return Create::eq<Ex::String>(a, b);
                default:
                    throw Utils::Error::Unexpected::Type(WHOAMI_WITH_SOURCE
                                                         "Unsupported expression type");
            }
        }

        /** An abbreviation for Utils::ThreadSafe::Mutable */
        template <typename T> using TSM = Utils::ThreadSafe::Mutable<T>;

        /** A helper function that tries to get an object from a cache
         *  Returns a pair; the first value is a boolean that stores if it was found
         *  The second value is the value that was found, or default constructed if not found
         *  Note that the second value is copied to ensure thread safety
         */
        template <typename Key, typename Value>
        static std::pair<bool, Value> get_from_cache(const TSM<std::map<Key, Value>> &tsm_cache,
                                                     const Key &key) {
            auto [cache, _] = tsm_cache.scoped_shared();
            if (const auto lookup { cache.find(key) }; lookup != cache.end()) {
                return { true, lookup->second };
            }
            return { false, {} };
        }

        /********************************************************************/
        /*                          Representation                          */
        /********************************************************************/

        /** Stores a symbol's annotations to be translocated from the pre-conversion expression
         *  to the post-abstraction expression symbol of the same name.
         */
        inline static thread_local std::map<std::string, Expression::Base::SPAV>
            symbol_annotation_translocation_data {};
    };

} // namespace Backend::Z3

#endif