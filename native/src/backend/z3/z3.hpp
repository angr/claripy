/**
 * @file
 * @brief This file defines the Z3 backend
 */
#ifndef R_SRC_BACKEND_Z3_Z3_HPP_
#define R_SRC_BACKEND_Z3_Z3_HPP_

#include "bool_tactic.hpp"
#include "dispatch.hpp"
#include "solver.hpp"

#include "../../error.hpp"
#include "../generic.hpp"


namespace Backend::Z3 {

    // Z3 global settings
    UTIL_RUN_FUNCTION_BEFORE_MAIN(z3::set_param, "rewriter.hi_fp_unspecified", rhfpu);

    /** The Z3 backend
     *  Warning: All Z3 backends within a given thread share their data
     */
    class Z3 final : public Generic<Z3, z3::expr> {
        ENABLE_UNITTEST_FRIEND_ACCESS;
        /** Allow Dispatch friend access */
        friend struct Dispatch<Z3>;
        // Disable implicits
        SET_IMPLICITS_NONDEFAULT_CTORS(Z3, delete);

        /** Convert v to an z3::expr_vector */
        inline z3::expr_vector to_expr_vec(z3::context &ctx, const std::vector<Expr::RawPtr> &v) {
            z3::expr_vector ret { ctx };
            for (uint32_t i { 0 }; i < v.size(); ++i) {
                ret.push_back(convert(v[i])); // TODO: find a more efficient way
            }
            return ret;
        }

      public:
        /** Used for static error checking in template injection */
        using IsZ3Bk = std::true_type;
        /** Z3 objects cannot hold annotations */
        static UTIL_CCBOOL apply_annotations = false;

        /** Constructor */
        inline Z3() noexcept = default;
        /** Destructor */
        inline ~Z3() noexcept = default;

        /********************************************************************/
        /*                        Function Overrides                        */
        /********************************************************************/

        /** The name of this backend */
        [[nodiscard]] inline const char *name() const noexcept final { return "z3"; }

        /** Simplify the given expr
         *  expr may not be nullptr
         */
        inline Expr::BasePtr simplify(const Expr::RawPtr expr) final {
            UTIL_ASSERT_NOT_NULL_DEBUG(expr);
            switch (expr->cuid) {
                case Expr::Bool::static_cuid: {
                    auto b_obj { convert(expr) };
                    b_obj = bool_simplify(b_obj);
                    return abstract(b_obj);
                }
                case Expr::BV::static_cuid: {
                    auto b_obj { convert(expr) };
                    b_obj = b_obj.simplify();
                    return abstract(b_obj);
                }
                default: {
                    Util::Log::info(
                        "Z3 Backend cannot simplify expr of type: ",
                        Util::LazyFunc { [](const auto e) noexcept { return e->type_name(); },
                                         std::move(expr) });
#ifdef DEBUG
                    auto ret { Expr::find(expr->hash) };
                    UTIL_ASSERT_EMPTY(Util::Err::HashCollision, ret.get() == expr);
                    return ret;
#else
                    return Expr::find(expr->hash);
#endif
                }
            }
        }

        /** Clears translocation data */
        inline void clear_persistent_data() final {
            Util::Log::warning("Z3 backend clearing persistent data...");
            tls.symbol_annotation_translocation_data.clear();
        }

        /********************************************************************/
        /*                         Member Functions                         */
        /********************************************************************/

        /** Define this thread as the main thread
         *  This should only be called once
         */
        static inline void set_main() {
            static std::atomic_bool done { false };
            const bool ok { not done.exchange(true) };
            UTIL_ASSERT(Util::Err::Usage, ok, "This function may only be called once");
            tls.main_thread = true;
#ifdef DEBUG
            main_set = true;
#endif
        }

        /** Interrupt this thread's z3 context */
        inline void interrupt() {
            tls.ctx.interrupt();
        }

        /** Clone the given solver */
        inline Solver clone(const Solver &s) {
            // https://github.com/Z3Prover/z3/issues/556
            return s.clone(tls.ctx);
        }

        /** Return a tls solver
         *  If timeout is not 0, timeouts will be configured for the solver, new or reused
         *  If max_memory is not 0, memory limits will be configured for the solver, new or reused
         *  Warning: solver is not saved locally if force_new is false
         */
        template <bool ForceNew = false>
        [[nodiscard]] inline std::shared_ptr<Solver> tls_solver(const unsigned timeout = 0,
                                                                const unsigned max_memory = 0) {
            auto ret { get_tls_solver<ForceNew>() };
            auto &slv { *ret };
            if (timeout) {
                if (slv->get_param_descrs().to_string().find("soft_timeout") != std::string::npos) {
                    slv->set("soft_timeout", timeout);
                    slv->set("solver2_timeout", timeout);
                }
                else {
                    slv->set("timeout", timeout);
                }
            }
            if (UNLIKELY(max_memory)) {
                slv->set("max_memory", max_memory);
            }
            return ret;
        }

        /** Add constraint to the solver, track if Track */
        template <bool Track = false> void add(Solver &solver, const Expr::RawPtr constraint) {
            add_helper<Track>(solver, &constraint, 1);
        }

        /** Add constraints to the solver, track if Track */
        template <bool Track = false>
        void add(Solver &solver, const std::vector<Expr::RawPtr> &constraints) {
            add_helper<Track>(solver, constraints.data(), constraints.size());
        }

        /** Check to see if the solver is in a satisfiable state */
        inline bool satisfiable(Solver &solver) const {
            return is_sat(solver, nullptr);
        }

        /** Check to see if the solver is in a satisfiable state */
        inline bool satisfiable(Solver &solver,
                                const std::vector<Expr::RawPtr> &extra_constraints) {
            const auto ec { to_expr_vec(solver->ctx(), extra_constraints) };
            return is_sat(solver, &ec);
        }

        /** Check if expr = sol is a solution to the given solver; none may be nullptr */
        inline bool solution(const Expr::RawPtr expr, const Expr::RawPtr sol, Solver &solver,
                             const std::vector<Expr::RawPtr> &extra_constraints) {
            auto ec { to_expr_vec(solver->ctx(), extra_constraints) };
            ec.push_back(convert(expr) == convert(sol)); // Debug verifies expr is not null
            return is_sat(solver, &ec);                  // Debug verifies non-null
        }

        /** Check to see if sol is a solution to expr w.r.t the solver; neither may be nullptr */
        inline bool solution(const Expr::RawPtr expr, const Expr::RawPtr sol, Solver &solver) {
            const static thread_local std::vector<Expr::RawPtr> s {};
            return solution(expr, sol, solver, s);
        }

        /** Find the min value of expr that satisfies solver; returns an I64 or U64 */
        template <bool Signed> inline auto min(const Expr::RawPtr expr, Solver &solver) {
            auto ec { to_expr_vec(solver->ctx(), {}) };
            return extrema<Signed, true>(expr, solver, std::move(ec));
        }

        /** Find the min value of expr that satisfies solver; returns an I64 or U64 */
        template <bool Signed>
        inline auto min(const Expr::RawPtr expr, Solver &solver,
                        const std::vector<Expr::RawPtr> &extra_constraints) {
            auto ec { to_expr_vec(solver->ctx(), extra_constraints) };
            return extrema<Signed, true>(expr, solver, std::move(ec));
        }

        /** Find the max value of expr that satisfies solver; returns an I64 or U64 */
        template <bool Signed> inline auto max(const Expr::RawPtr expr, Solver &solver) {
            auto ec { to_expr_vec(solver->ctx(), {}) };
            return extrema<Signed, false>(expr, solver, std::move(ec));
        }

        /** Find the max value of expr that satisfies solver; returns an I64 or U64 */
        template <bool Signed>
        inline auto max(const Expr::RawPtr expr, Solver &solver,
                        const std::vector<Expr::RawPtr> &extra_constraints) {
            auto ec { to_expr_vec(solver->ctx(), extra_constraints) };
            return extrema<Signed, false>(expr, solver, std::move(ec));
        }

        /** Return the unsat core from the solver
         *  Warning: This assumes all of solver->assertions were added by add<true>
         */
        inline std::vector<Expr::BasePtr> unsat_core(const Solver &solver) {
            const auto cores { get_tracked<false>(solver->unsat_core()) };
            // Create ret, reserve tracked.size() (probably larger than needed)
            std::vector<Expr::BasePtr> ret;
            const auto len { cores.size() };
            ret.reserve(len);
            // For each assertion
            const auto assertions { solver->assertions() };
            const auto a_len { assertions.size() };
            for (unsigned int i { 0 }; i < a_len; ++i) {
                // Extract the hash of the next assertion
                const auto a_i { assertions[i] };
#ifdef DEBUG
                UTIL_ASSERT(Util::Err::Unknown, a_i.num_args() >= 2, "Malformed assertion: ", a_i);
#endif
                const auto [hash, tracked] { extract_hash(a_i.arg(0)) }; // Get hash from name
                // Skip untracked / non-core assertions
                if (tracked && cores.find(hash) != cores.end()) {
                    // Get the object either by a hash lookup or by constructing it if that fails
                    if (auto lookup { Expr::find(hash) }; lookup) {
                        ret.emplace_back(std::move(lookup));
                    }
                    else {
                        ret.emplace_back(abstract(a_i.arg(1)));
#ifdef DEBUG
                        if (ret.back()->hash != hash) {
                            Util::Log::warning(WHOAMI
                                               "Reconstruction had a different hash. "
                                               "Perhaps this is caused by changing BigInt modes?");
                        }
#endif
                    }
                }
            }
            return ret;
        }

        /** Evaluate expr, return up to n different solutions
         *  No pointers may be nullptr
         */
        inline std::vector<Op::PrimVar> eval(const Expr::RawPtr expr, Solver &solver,
                                             const U64 n_sol,
                                             const std::vector<Expr::RawPtr> &extra_constraints) {
            auto ec { to_expr_vec(solver->ctx(), extra_constraints) };
            std::vector<Op::PrimVar> ret;
            ret.reserve(n_sol); // We do not resize as we may return < n_sol
            const z3::expr conv { convert(expr) };
            if (n_sol > 1) {
                solver->push();
            }
            // Repeat for each new solution
            for (U64 iter { 0 }; iter < n_sol; ++iter) {
                if (not is_sat(solver, &ec)) {
                    // No point in search further, return what we have
                    break;
                }
                // Extract solutions
                const z3::model model { solver->get_model() };
                const auto evaled { model.eval(conv, true) };
                ret.emplace_back(abstract_to_prim(evaled));
                // Construct extra constraints to prevent solution duplication
                if (iter + 1 != n_sol) {
                    solver->add(conv != evaled);
                }
            }
            if (n_sol > 1) {
                solver->pop();
            }
            return ret;
        }

        /** Evaluate expr, return up to n different solutions
         *  No pointers may be nullptr
         */
        inline std::vector<Op::PrimVar> eval(const Expr::RawPtr expr, Solver &s, const U64 n) {
            return eval(expr, s, n, {});
        }

        /** Evaluate every expr, return up to n different solutions
         *  No pointers may be nullptr
         */
        inline std::vector<std::vector<Op::PrimVar>>
        batch_eval(const std::vector<Expr::RawPtr> &exprs, Solver &s, const U64 n,
                   const std::vector<Expr::RawPtr> &extra_constraints) {
            if (UNLIKELY(exprs.size() == 0)) {
                return {};
            }
            if (UNLIKELY(exprs.size() == 1)) { // Why we prefer eval to batch
                Util::Log::info(WHOAMI
                                "called on exprs of size 1; eval is more efficient for this");
                const auto sols { eval(exprs[0], s, n) };
                std::vector<std::vector<Op::PrimVar>> ret;
                ret.reserve(sols.size());
                for (const auto &i : sols) {
                    ret.emplace_back(std::vector<Op::PrimVar> { i }); // Why we prefer eval to batch
                }
                return ret;
            }
            std::vector<z3::expr> converted;
            converted.reserve(exprs.size());
            for (const Expr::RawPtr i : exprs) {
                converted.emplace_back(convert(i));
            }
            return batch_eval(converted, s, n, to_expr_vec(s->ctx(), extra_constraints));
        }

        /** Evaluate every expr, return up to n different solutions
         *  No pointers may be nullptr
         */
        inline std::vector<std::vector<Op::PrimVar>>
        batch_eval(const std::vector<Expr::RawPtr> &exprs, Solver &s, const U64 n) {
            return batch_eval(exprs, s, n, {});
        }

      private:
        /** This dynamic dispatcher converts expr into a backend object
         *  All arguments of expr that are not primitives have been
         *  pre-converted into backend objects and are in args
         *  Arguments must be popped off the args stack if used
         *  expr may not be nullptr
         *  Warning: This function may internally do unchecked static casting, we permit this
         *  *only* if the cuid of the expr is of or derive from the type being cast to.
         */
        inline z3::expr dispatch_conversion(const Expr::RawPtr expr,
                                            std::vector<const z3::expr *> &args) final {
            return Dispatch<Z3>::dispatch_conversion(
                expr, args, tls.symbol_annotation_translocation_data, *this);
        }

        /** Abstract a backend object into a claricpp expr */
        inline AbstractionVariant
        dispatch_abstraction(const z3::expr &b_obj, std::vector<AbstractionVariant> &args) final {
            return Dispatch<Z3>::dispatch_abstraction(b_obj, args,
                                                      tls.symbol_annotation_translocation_data);
        }

        /********************************************************************/
        /*                     Private Helper Functions                     */
        /********************************************************************/

        /** Disable Z3 sigint handling for non-main-thread solvers */
        inline void no_sigint(Solver &s) {
#ifdef DEBUG
            UTIL_ASSERT(Util::Err::Usage, main_set, "Mark the main thread!");
#endif
            if (not tls.main_thread) {
                s->set("ctrl_c", false);
            }
        }

        /** Return a tls solver
         *  Warning: solver is not saved locally if force_new is false
         */
        template <bool ForceNew> [[nodiscard]] inline std::shared_ptr<Solver> get_tls_solver() {
            if constexpr (ForceNew) {
                auto ret { std::make_shared<Solver>(z3::solver { tls.ctx }) };
                no_sigint(*ret);
                return ret;
            }
            else if (UNLIKELY(tls.solver == nullptr)) {
                tls.solver = std::make_shared<Solver>(z3::solver { tls.ctx });
                no_sigint(*(tls.solver));
            }
            return tls.solver;
        }

        /** Extracts the hash from the boolean z3::expr expr named: 'H' + X
         *  Returns {<Hash>, <Success>}
         *  If the name does not start with H0x, success is set to false
         *  Assumes X is a string output by Util::to_hex
         *  Warning: If X is not a string output by Util::hex, we have undefined behavior
         *  Note: This function must be updated in tandem with add_helper
         */
        inline std::pair<Hash::Hash, bool> extract_hash(const z3::expr &expr) const {
            // Note that we use the lower level API to avoid a string allocation for speed
            const char *str { Z3_ast_to_string(expr.ctx(), expr) };
            if (std::strncmp(str, "H0x", 3)) { // Prefix test
                return { 0, false };
            }
            Hash::Hash ret { 0 };
            for (str += 3; str[0] != '\0'; ++str) { // Remove prefix H0x then convert the hex
                ret <<= 4;
                ret += Util::hex_to_num(str[0]);
            }
            return { ret, true };
        }

        /** Returns the hashes of tracked constraints in input
         *  Assumes all hashes were inserted by add_helper
         *  If Arg0 is true, assumes arg(0) of each element is what stores the name
         *  If Arg0 is false, assumes the element itself is the name.
         */
        template <bool Arg0> std::set<Hash::Hash> get_tracked(const z3::expr_vector &input) const {
            std::set<Hash::Hash> ret;
            // For each assertion, extract the name (the first child as a string)
            // Convert the name to a hash with stoi-like functions, and save the hash
            for (unsigned int i { 0 }; i < input.size(); ++i) {
                const auto bool_name { Arg0 ? input[i].arg(0) : input[i] };
                const auto [hash, tracked] { extract_hash(bool_name) };
                if (tracked) {
#ifdef DEBUG
                    const auto [_, success] { ret.emplace(hash) };
                    if (not success) {
                        Util::Log::warning(WHOAMI " potential hash collision detected.");
                        (void) _;
                    }
#else
                    (void) ret.emplace(hash);
#endif
                }
            }
            return ret;
        }

        /** Add constraints to the solver, track if Track
         *  Note: Each constraint is tracked with the name 'H' + str(c->hash)
         *  Note: This function must be updated in tandem with extract_hash
         */
        template <bool Track>
        void add_helper(Solver &solver, CTSC<Expr::RawPtr> constraints, const U64 c_len) {
            if constexpr (not Track) {
                for (U64 i { 0 }; i < c_len; ++i) {
                    solver->add(convert(constraints[i]));
                }
            }
            else {
                std::set<Hash::Hash> tracked { get_tracked<true>(solver->assertions()) };
                char buf[1 + Util::to_hex_max_len<Hash::Hash>];
                for (U64 i { 0 }; i < c_len; ++i) {
                    // If the new constraint is not track, track it
                    const Hash::Hash c_hash { constraints[i]->hash };
                    if (const auto lookup { tracked.find(c_hash) }; lookup == tracked.end()) {
                        // We use to_hex to avoid heap allocations due to temporary strings
                        // This also leads to avoiding much the same when converting back
                        buf[0] = 'H';
                        (void) Util::to_hex(c_hash, &buf[1]); // Populates buf
                        solver->add(convert(constraints[i]), solver->ctx().bool_const(buf));
                        tracked.insert(c_hash);
                    }
                }
            }
        }

        /** Check to see if the solver is in a satisfiable state */
        inline bool is_sat(Solver &solver, CTSC<z3::expr_vector> ec) const {
            z3::check_result res { (ec == nullptr ? solver->check() : solver->check(*ec)) };
            if (UNLIKELY(res == z3::unknown)) {
                // If the solvers were interrupted oddly, raise the proper error exception
                const std::string reason { solver->reason_unknown() };
#define M_EXCEPT_IF(ERR, ...)                                                                      \
    {                                                                                              \
        static const std::set<std::string> s { __VA_ARGS__ };                                      \
        UTIL_ASSERT(ERR, s.find(reason) != s.end(), reason);                                       \
    }
                M_EXCEPT_IF(Util::Err::Python::KeyboardInterrupt, "interrupted",
                            "interrupted from keyboard");
                M_EXCEPT_IF(Error::Backend::SolverInterrupt, "timeout",
                            "max. resource limit exceeded", "max. memory exceeded");
#undef M_EXCEPT_IF
            }
            return res == z3::sat;
        }

        /** Return up to n_sol different solutions of solver given exprs, where exprs.size() > 1
         *  No pointers may be nullptr
         */
        inline std::vector<std::vector<Op::PrimVar>>
        batch_eval(const std::vector<z3::expr> exprs, Solver &solver, const U64 n_sol,
                   const z3::expr_vector &extra_constraints) const {
            UTIL_ASSERT(Util::Err::Usage, exprs.size() > 1,
                        "should only be called when exprs.size() > 1");
            // Prep
            solver->push();
            std::vector<std::vector<Op::PrimVar>> ret;
            ret.reserve(n_sol); // We do not resize as we may return < n_sol
            // Repeat for each new solution
            std::vector<z3::expr> z3_sol;
            for (U64 iter { 0 }; iter < n_sol; ++iter) {
                if (not is_sat(solver, &extra_constraints)) {
                    // No point in search further, return what we have
                    break;
                }

                // Prep loop body
                if (iter) {
                    z3_sol.clear();
                }
                z3_sol.reserve(exprs.size());
                ret.emplace_back(); // Create a new vector

                // Extract solutions
                const z3::model model { solver->get_model() };
                for (const auto &expr : exprs) {
                    z3_sol.emplace_back(model.eval(expr, true));
                    ret[iter].emplace_back(abstract_to_prim(z3_sol.back()));
                }

                // Construct extra constraints to prevent solution duplication
                if (iter + 1 != n_sol) {
                    z3::expr current_sol { exprs[0] == z3_sol[0] };
                    for (U64 i { 1 }; i < exprs.size(); ++i) {
                        current_sol = current_sol && (exprs[i] == z3_sol[i]);
                    }
                    solver->add(not current_sol);
                }
            }
            // Cleanup
            solver->pop();
            return ret;
        }

        /** The method used to simplify z3 boolean exprs*/
        inline z3::expr bool_simplify(const z3::expr &expr) const {
            return tls.bt(expr);
        }

        /** Abstract b_obj to a type in PrimVar */
        inline Op::PrimVar abstract_to_prim(const z3::expr &b_obj) const {
#ifndef BACKEND_DISABLE_ABSTRACTION_CACHE
            auto &abstraction_prim_cache { tls.abstract_prim_cache };
            const auto hash { b_obj.hash() };
            if (const auto lookup { abstraction_prim_cache.find(hash) };
                lookup != abstraction_prim_cache.end()) {
                return lookup->second;
            }
            auto ret { Dispatch<Z3>::dispatch_abstraction_to_prim(
                b_obj) }; // Not const for ret move
            Util::map_add(abstraction_prim_cache, hash, ret);
            return ret;
#else
            return Dispatch<Z3>::dispatch_abstraction_to_prim(b_obj);
#endif
        }

        /** Find the min/max value of expr that satisfies solver; returns an I64 or U64 */
        template <bool Signed, bool Minimize>
        inline auto extrema(const Expr::RawPtr raw_expr, Solver &solver,
                            z3::expr_vector &&extra_constraints) {
            // Check input
            using Usage = Util::Err::Usage;
            UTIL_ASSERT_NOT_NULL_DEBUG(raw_expr);
#ifdef DEBUG
            UTIL_ASSERT(Usage, CUID::is_t<Expr::BV>(raw_expr), "expr must be a BV");
#endif
            const auto len { Expr::bit_length(raw_expr) };
            UTIL_ASSERT(Usage, len <= 64, "ret cannot be called on BV wider than 64 bits");
            z3::expr expr { convert(raw_expr) };

            // Starting interval and comparators
            using Integer = std::conditional_t<Signed, I64, U64>;
            using Z3Integer = std::conditional_t<Signed, int64_t, uint64_t>;
#define M_MAX_S(S) ((Integer { 1 } << (len - S)) - 1 + (Integer { 1 } << (len - S)))
            Integer hi { Signed ? M_MAX_S(2) : M_MAX_S(1) };
            Integer lo { Signed ? (-hi - 1) : 0 };
#undef M_MAX_S

            // Inline-able lambdas to for clarity
            const auto to_z3 { [&len](const Integer i) {
                return tls.ctx.bv_val(static_cast<Z3Integer>(i), Util::narrow<unsigned>(len));
            } };
            const auto ge { [](const z3::expr &a, const z3::expr &b) {
                return (Signed ? z3::sge(a, b) : z3::uge(a, b));
            } };
            const auto le { [](const z3::expr &a, const z3::expr &b) {
                return (Signed ? z3::sle(a, b) : z3::ule(a, b));
            } };

            // Binary search
            while (hi > lo + 1) { // Difference of 1 instead of 0 to prevent infinite loop
                // Add new bounding constraints
                const Integer middle { Util::avg(hi, lo) };
                extra_constraints.push_back(ge(expr, to_z3(Minimize ? lo : middle)) &&
                                            le(expr, to_z3(Minimize ? middle : hi)));
                // Binary search
                const bool sat { is_sat(solver, &extra_constraints) };
                (sat == Minimize ? hi : lo) = middle;
                extra_constraints.pop_back();
            }

            // Last step of binary search
            extra_constraints.push_back(expr == to_z3(Minimize ? lo : hi));
            const Integer ret { Minimize == is_sat(solver, &extra_constraints) ? lo : hi };
            return ret;
        }

        /********************************************************************/
        /*                      Private Helper Classes                      */
        /********************************************************************/

        /** Holds and initializes the thread_local z3 data */
        struct TLS final {

            /** If this is the main thread */
            bool main_thread { false };
            /** The z3 context this uses */
            z3::context ctx {};
            /** The BoolTactic the z3 backend will use */
            BoolTactic bt { ctx };
            /** The z3 solver to be used by this backend */
            std::shared_ptr<Solver> solver { nullptr };

            /** Stores a symbol's annotations to be translocated from the pre-conversion expr
             *  to the post-abstraction expr symbol of the same name.
             */
            SymAnTransData symbol_annotation_translocation_data {};
#ifndef BACKEND_DISABLE_ABSTRACTION_CACHE
            /** A cache for abstractions to primitives */
            std::map<Hash::Hash, PrimVar> abstract_prim_cache {};
#endif
        };

        /********************************************************************/
        /*                          Representation                          */
        /********************************************************************/

        /** Thread local data the Z3 backend uses
         *  All Z3 backends share this
         */
        static thread_local TLS tls;

#ifdef DEBUG
        /** True iff the main thread was noted */
        static std::atomic_bool main_set;
#endif
    };

} // namespace Backend::Z3

#endif
