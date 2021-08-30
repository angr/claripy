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
        /********************************************************************/
        /*                        Function Overrides                        */
        /********************************************************************/

        /** Destructor */
        ~Z3() noexcept override = default;

        /** Clears translocation data */
        inline void clear_persistent_data() override final {
            Utils::Log::warning("Z3 backend clearing persistent data...");
            symbol_annotation_translocation_data.clear();
        }

        /** The name of this backend */
        [[nodiscard]] inline const char *name() const noexcept override final { return "z3"; }

        /** Simplify the given expression
         *  expr may not be nullptr
         */
        inline Expression::BasePtr simplify(const Expression::RawPtr expr) override final {
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

        /********************************************************************/
        /*                         Member Functions                         */
        /********************************************************************/

        /** Return a tls solver
         *  If timeout is not 0, timeouts will be configured for the solver
         *  Warning: resets the tls solver if force_new is false
         */
        [[nodiscard]] inline std::shared_ptr<z3::solver>
        tls_solver(const unsigned timeout = 0, const bool force_new = false) const {
            auto ret { get_tls_solver(force_new) };
            if (timeout != 0) {
                if (ret->get_param_descrs().to_string().find("soft_timeout") !=
                    std::string::npos) {
                    ret->set("soft_timeout", timeout);
                    ret->set("solver2_timeout", timeout);
                }
                else {
                    ret->set("timeout", timeout);
                }
            }
            return ret;
        }

        /** Add constraint to the solver, track if Track */
        template <bool Track = false>
        void add(z3::solver &solver, const Expression::RawPtr &constraint) {
            const Expression::RawPtr arr[] { constraint };
            add_helper<Track>(solver, arr, 1);
        }

        /** Add constraints to the solver, track if Track */
        template <bool Track = false>
        void add(z3::solver &solver, const std::vector<Expression::RawPtr> &constraints) {
            add_helper<Track>(solver, constraints.data(), constraints.size());
        }

        /** Check to see if the solver is in a satisfiable state */
        inline bool satisfiable(z3::solver &solver) {
            return solver.check() == z3::check_result::sat;
            // @todo: model callback
        }

        /** Check to see if the solver is in a satisfiable state */
        inline bool satisfiable(z3::solver &solver,
                                const std::vector<Expression::RawPtr> &extra_constraints) {
            ECHelper ec { *this, solver, extra_constraints };
            return satisfiable(solver);
        }

        /** Check if expr = sol is a solution to the given solver; none may be nullptr */
        inline bool solution(const Expression::RawPtr &expr, const Expression::RawPtr &sol,
                             z3::solver &solver,
                             const std::vector<Expression::RawPtr> &extra_constraints) {
            ECHelper ec { *this, solver, extra_constraints };
            if (!ec.pushed()) {
                solver.push();
                ec.pushed(true);
            }
            const auto eq { to_eq(expr, sol) }; // Debug verifies expr is not null
            solver.add(convert(eq.get()));
            return satisfiable(solver, extra_constraints); // Debug verifies non-null
        }

        /** Check to see if sol is a solution to expr w.r.t the solver; neither may be nullptr */
        inline bool solution(const Expression::RawPtr &expr, const Expression::RawPtr &sol,
                             z3::solver &solver) {
            static thread_local std::vector<Expression::RawPtr> s;
            return solution(expr, sol, solver, s);
        }

        /** Find the min value of expr that satisfies solver; returns an int64_t or uint64_t */
        template <bool Signed> inline auto min(const z3::expr &expr, z3::solver &solver) {
            return extrema<Signed, true>(expr, solver);
        }

        /** Find the min value of expr that satisfies solver; returns an int64_t or uint64_t */
        template <bool Signed>
        inline auto min(const z3::expr &expr, z3::solver &solver,
                        const std::vector<Expression::RawPtr> &extra_constraints) {
            ECHelper ec { *this, solver, extra_constraints };
            return min<Signed>(expr, solver);
        }

        /** Find the max value of expr that satisfies solver; returns an int64_t or uint64_t */
        template <bool Signed> inline auto max(const z3::expr &expr, z3::solver &solver) {
            return extrema<Signed, false>(expr, solver);
        }

        /** Find the max value of expr that satisfies solver; returns an int64_t or uint64_t */
        template <bool Signed>
        inline auto max(const z3::expr &expr, z3::solver &solver,
                        const std::vector<Expression::RawPtr> &extra_constraints) {
            ECHelper ec { *this, solver, extra_constraints };
            return max<Signed>(expr, solver);
        }

        /** Return the unsat core from the solver
         *  Warning: This assumes all of solver's assertions were added by add<true>
         */
        inline std::vector<Expression::BasePtr> unsat_core(z3::solver &solver) {
            std::vector<Expression::BasePtr> ret;
            const auto cores { solver.unsat_core() };
            const auto len { cores.size() };
            ret.reserve(len);
            Utils::Log::info("Len: ", len);
            z3::expr_vector assertions { solver.ctx() };
            std::map<Hash::Hash, int> indexes;
            for (unsigned i { 0 }; i < len; ++i) {
                const auto child { cores[static_cast<int>(i)] };
                const Hash::Hash h { extract_hash(child) };
                // First try to lookup the child by the hash
                if (auto lookup { Expression::find(h) }; lookup != nullptr) {
                    Utils::Log::info(__LINE__);
                    ret.emplace_back(std::move(lookup));
                    continue;
                }
                // Otherwise, abstract assertion object
                if (assertions.size() == 0) {
                    assertions = solver.assertions();
                    const auto len_a { assertions.size() };
                    for (int k = 0; k < static_cast<int>(len_a); ++k) {
                        indexes.emplace(extract_hash(assertions[k]), k);
                    }
                }
                ret.emplace_back(abstract(assertions[indexes[h]]));
            }
            return ret;
        }

      private:
        /********************************************************************/
        /*                     Private Helper Functions                     */
        /********************************************************************/

        /** Return a tls solver
         *  Warning: resets the tls solver if force_new is false
         */
        [[nodiscard]] inline std::shared_ptr<z3::solver>
        get_tls_solver(const bool force_new = false) const {
            static thread_local std::shared_ptr<z3::solver> s {};
            if (UNLIKELY(s == nullptr)) {
                s.reset(new z3::solver { Private::tl_ctx }); // NOLINT
            }
            if (force_new) {
                return std::make_shared<z3::solver>(Private::tl_ctx);
            }
            else {
                s->reset();
                return s;
            }
        }

        /** Extracts the hash from the boolean z3::expr expr named: |hash| */
        inline Hash::Hash extract_hash(const z3::expr &expr) {
            // Note that we use the lower level API so we can do a +1, otherwise
            // we would need to erase the first character of the string, which is slow
            std::string hash_s { Z3_ast_to_string(expr.ctx(), expr) + 1 };
            hash_s.pop_back();
            static_assert(std::is_same_v<Hash::Hash, uint64_t>,
                          "stoull must be replaced with something which outputs a Hash");
            static_assert(sizeof(unsigned long long) == sizeof(Hash::Hash),
                          "stoull must be replaced with something which outputs a Hash");
            // Technically uint64_t might be a ULL, but this should be fine given the above
            return std::stoull(hash_s);
        }

        /** Returns the hashes of tracked constraints of solver
         *  Assumes all hashes were inserted by add_helper and thus each name is a hash
         */
        inline std::set<Hash::Hash> get_tracked(z3::solver &solver) {
            std::set<Hash::Hash> tracked;
            const z3::expr_vector assertions { solver.assertions() };
            const auto size { assertions.size() };
            // For each assertion, extract the name (the first child as a string)
            // Convert the name to a hash with stoi-like functions, and save the hash
            for (unsigned i { 0 }; i < size; ++i) {
                const auto bool_name { assertions[Utils::sign(i)].arg(0) };
                tracked.emplace(extract_hash(bool_name));
            }
            return tracked;
        }

        /** Add constraints to the solver, track if Track
         *  @todo See if we can cast the ull to a char * instead of convert?
         */
        template <bool Track>
        void add_helper(z3::solver &solver, Constants::CTSC<Expression::RawPtr> constraints,
                        const Constants::UInt c_len) {
            if constexpr (!Track) {
                for (Constants::UInt i { 0 }; i < c_len; ++i) {
                    solver.add(convert(constraints[i]));
                }
            }
            else {
                const std::set<Hash::Hash> tracked { get_tracked(solver) };
                for (Constants::UInt i { 0 }; i < c_len; ++i) {
                    // If the new constraint is not track, track it
                    const Hash::Hash c_hash { constraints[i]->hash };
                    if (const auto lookup { tracked.find(c_hash) }; lookup == tracked.end()) {
                        solver.add(convert(constraints[i]),
                                   solver.ctx().bool_const(std::to_string(c_hash).c_str()));
                    }
                }
            }
        }

        /** The method used to simplify z3 boolean expressions*/
        inline z3::expr bool_simplify(const z3::expr &expr) {
            static thread_local BoolTactic bt {};
            return bt(expr);
        }

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

        /** Coerce a PrimVar into a T via static_cast-ing
         *  This assumes the value of x will fit within T
         *  This assumes the PrimVar is set to a BV type
         */
        template <typename T> T coerce_to(PrimVar &&p) {
            using Usage = Utils::Error::Unexpected::Usage;
            switch (p.index()) {
                /** A local macro used for consistency */
#define CASE_B(INDEX, TYPE)                                                                       \
    case INDEX: {                                                                                 \
        UTILS_VARIANT_VERIFY_INDEX_TYPE_IGNORE_CONST(p, INDEX, TYPE);                             \
        return static_cast<T>(std::get<TYPE>(p));                                                 \
    }
                CASE_B(5, uint8_t)
                CASE_B(6, uint16_t)
                CASE_B(7, uint32_t)
                CASE_B(8, uint64_t)
#undef CASE_B
                case 9: {
                    UTILS_VARIANT_VERIFY_INDEX_TYPE_IGNORE_CONST(p, 9, BigInt);
                    const auto &bi = std::get<BigInt>(p);
                    Utils::affirm<Usage>(bi.bit_length < 64, WHOAMI_WITH_SOURCE
                                         "Bit length of given PrimVar is too long");
                    return static_cast<T>(bi.value);
                }
                default:
                    throw Usage(WHOAMI_WITH_SOURCE "Invalid PrimVar given");
            }
        }

        /** Create a == b; neither may be nullptr */
        static inline Expression::BasePtr to_eq(const Expression::RawPtr &a_raw,
                                                const Expression::RawPtr &b_raw) {
            UTILS_AFFIRM_NOT_NULL_DEBUG(a_raw);
            UTILS_AFFIRM_NOT_NULL_DEBUG(b_raw);
            namespace Ex = Expression;
            const auto a { Ex::find(a_raw->hash) };
            const auto b { Ex::find(b_raw->hash) };
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

        /** Find the min/max value of expr that satisfies solver; returns an int64_t or uint64_t */
        template <bool Signed, bool Minimize>
        inline auto extrema(const z3::expr &expr, z3::solver &solver) {
            // Check input
            using Usage = Utils::Error::Unexpected::Usage;
#ifdef DEBUG
            Utils::affirm<Usage>(expr.is_bv(), WHOAMI_WITH_SOURCE "ret can only be called on BVs");
#endif
            const unsigned len { expr.get_sort().bv_size() };
            Utils::affirm<Usage>(len <= 64, WHOAMI_WITH_SOURCE
                                 "ret cannot be called on BV wider than 64 bits");

            // Starting interval and comparators
            using Integer = std::conditional_t<Signed, int64_t, uint64_t>;
            /** A local macro for brevity */
#define MAX_S(S) ((Integer { 1 } << (len - S)) - 1 + (Integer { 1 } << (len - S)))
            Integer hi { Signed ? MAX_S(2) : MAX_S(1) };
            Integer lo { Signed ? (-hi - 1) : 0 };
#undef MAX_S

            // Inline-able lambdas to for clarity
            const auto to_z3 { [&len](const Integer i) {
                return Private::tl_ctx.bv_val(i, len);
            } };
            const auto ge { [](const z3::expr &a, const z3::expr &b) {
                return (Signed ? z3::sge(a, b) : z3::uge(a, b));
            } };
            const auto le { [](const z3::expr &a, const z3::expr &b) {
                return (Signed ? z3::sle(a, b) : z3::ule(a, b));
            } };
            const auto extreme = [](const Integer a, const Integer b) constexpr {
                return (Minimize ? std::min(a, b) : std::max(a, b));
            }; // No {} initialization because clang-format has trouble with constexpr lambdas

            // Binary search
            Integer ret { Minimize ? hi : lo };
            bool pushed { false }; // The number of stack frames pushed
            while (hi > lo + 1) {  // Difference of 1 instead of 0 to prevent infinite loop
                // Protect the current solver state
                if (!pushed) {
                    solver.push();
                    pushed = true;
                }
                // Add new bounding constraints
                const Integer middle { Utils::avg(hi, lo) };
                solver.add(ge(expr, to_z3(Minimize ? lo : middle)));
                solver.add(le(expr, to_z3(Minimize ? middle : hi)));
                // If the constraints are good, save the info; if bad reset the solver frame
                if (solver.check() == z3::sat) {
                    (Minimize ? hi : lo) = middle;
                    const auto model { solver.get_model() };
                    ret = extreme(ret, coerce_to<Integer>(prim_from_model(model, expr)));
                }
                else {
                    (Minimize ? lo : hi) = middle;
                    solver.pop();
                    pushed = false;
                }
            }

            // Last step of binary search
            if (!pushed) {
                solver.push();
            }
            solver.add(expr == to_z3(Minimize ? lo : hi));
            ret = extreme(ret, Minimize == (solver.check() == z3::sat) ? lo : hi);
            solver.pop();
            return ret;
        }

        /********************************************************************/
        /*                      Private Helper Classes                      */
        /********************************************************************/

        /** Adds extra constraints to a z3 solver, pops them on destruction */
        class ECHelper final {
          public:
            /** Constructor
             *  solver may not be nullptr
             */
            inline ECHelper(Z3 &bk, z3::solver &s,
                            const std::vector<Expression::RawPtr> &extra_constraints)
                : z3 { bk }, solver { s }, act { extra_constraints.size() > 0 } {
                if (act) {
                    solver.push();
                    for (auto &i : extra_constraints) {
                        solver.add(z3.convert(i));
                    }
                }
            }
            /** Destructor */
            inline ~ECHelper() {
                if (act) {
                    solver.pop();
                }
            }
            /** Setter */
            inline void pushed(const bool b) noexcept { act = b; }
            /** Getter */
            inline bool pushed() const noexcept { return act; }

          private:
            /** The z3 instance to use */
            Z3 &z3;
            /** The solver */
            z3::solver &solver;
            /** True if extra_constraints is non-empty */
            bool act;
        };

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
