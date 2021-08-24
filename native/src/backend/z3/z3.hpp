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

    // Z3 global settings
    UTILS_RUN_FUNCTION_BEFORE_MAIN(z3::set_param, "rewriter.hi_fp_unspecified", rhfpu);

    /** The Z3 backend */
    class Z3 final : public Z3Super {
        ENABLE_UNITTEST_FRIEND_ACCESS;
        static_assert(!use_apply_annotations, "Z3 objects do not support holding annotations");

      public:
        /************************************************/
        /*              Function Overrides              */
        /************************************************/

        /** Destructor */
        ~Z3() noexcept override = default;

        /** Clears translocation data */
        inline void clear_persistent_data() override final {
            symbol_annotation_translocation_data.clear();
        }

        /** The name of this backend */
        [[nodiscard]] inline const char *name() const noexcept override final { return "z3"; }

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

        /************************************************/
        /*               Member Function                */
        /************************************************/

        /** Create a tls solver */
        [[nodiscard]] inline std::shared_ptr<z3::solver> new_tls_solver() const {
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

        /** The method used to simplify z3 boolean expressions*/
        inline z3::expr bool_simplify(const z3::expr &expr) {
            static thread_local BoolTactic bt {};
            return bt(expr);
        }

        /** Find the min value of expr that satisfies solver; returns an int64_t or uint64_t */
        template <bool Signed> inline auto min(const z3::expr &expr, z3::solver &solver) {
            // Check input
            using Usage = Utils::Error::Unexpected::Usage;
#ifdef DEBUG
            Utils::affirm<Usage>(expr.is_bv(), WHOAMI_WITH_SOURCE "min can only be called on BVs");
#endif
            const unsigned len { expr.get_sort().bv_size() };
            Utils::affirm<Usage>(len <= 64, WHOAMI_WITH_SOURCE
                                 "min cannot be called on BV wider than 64 bits");

            // Starting interval and comparators
            using Integer = std::conditional_t<Signed, int64_t, uint64_t>;
            Integer lo { std::numeric_limits<Integer>::min() };
            Integer hi { std::numeric_limits<Integer>::max() };
            auto to_z3 { [](const Integer i) { return Private::tl_ctx.bv_val(i, 64_ui); } };

            // Binary search
            Integer min { hi };
            unsigned n_push { 0 }; // The number of stack frames pushed
            while (hi - lo > 1) {  // Difference of 1 instead of 0 to prevent infinite loop
                // Protect the current solver state
                if (n_push == 0) {
                    solver.push();
                    n_push = 1;
                }
                // Add new bounding constraints
                const Integer middle { (hi / 2) + (lo / 2) }; // Not (hi+lo)/2 b/c overflow
                if constexpr (Signed) {
                    solver.add(z3::sge(expr, to_z3(lo)), z3::sle(expr, to_z3(middle)));
                }
                else {
                    solver.add(z3::uge(expr, to_z3(lo)), z3::ule(expr, to_z3(middle)));
                }
                // If the contraints are good, save the info; if bad reset the current solver frame
                if (solver.check() == z3::sat) {
                    const auto model { solver.get_model() };
                    const auto val { std::get<uint64_t>(prim_from_model(model, expr)) };
                    min = std::min(min, static_cast<Integer>(val)); // Changes sign if needed
                    hi = middle;
                }
                else {
                    lo = middle;
                    solver.pop();
                    n_push = 0;
                }
            }

            // Last step of binary search
            if (hi == lo) {
                min = std::min(min, lo);
            }
            // hi - lo == 1
            else {
                ++n_push;
                solver.push();
                solver.add(expr == to_z3(lo));
                min = std::min(min, (solver.check() == z3::sat) ? lo : hi);
            }

            // Restore the solver state and return the min
            solver.pop(n_push);
            return min;
        }

      private:
        /** Extract a primitive from a model
         * @todo test
         */
        inline PrimVar prim_from_model(const z3::model &m, const z3::expr &e) {
            const auto evaled { m.eval(e, true) };
            return abstract_to_prim(evaled);
        }

        /** Abstract b_obj to a type in PrimVar */
        inline PrimVar abstract_to_prim(const z3::expr &b_obj) {
#ifndef BACKEND_DISABLE_ABSTRACTION_CACHE
            const auto hash { b_obj.hash() };
            if (const auto lookup { abstraction_prim_cache.find(hash) };
                lookup != abstraction_prim_cache.end()) {
                return lookup->second;
            }
            auto ret { Private::dispatch_abstraction_to_prim(b_obj) };
            abstraction_prim_cache.emplace(hash, ret); // Not const for move ret purposes
            return ret;
#else
            return Private::dispatch_abstraction_to_prim(b_obj);
#endif
        }

        /** Create a == b; neither may be nullptr */
        static inline Expression::BasePtr to_eq(const Expression::BasePtr &a,
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

        /********************************************************************/
        /*                          Representation                          */
        /********************************************************************/

        /** Stores a symbol's annotations to be translocated from the pre-conversion expression
         *  to the post-abstraction expression symbol of the same name.
         */
        inline static thread_local std::map<std::string, Expression::Base::SPAV>
            symbol_annotation_translocation_data {};

#ifndef BACKEND_DISABLE_ABSTRACTION_CACHE
        /** A cache for abstractions to primitives */
        inline static thread_local std::map<Hash::Hash, PrimVar> abstract_prim_cache;
#endif
    };

} // namespace Backend::Z3

#endif