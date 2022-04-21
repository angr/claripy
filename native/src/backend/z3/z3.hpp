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

        /** Return a tls solver
         *  If timeout is not 0, timeouts will be configured for the solver, new or reused
         *  Warning: solver is not saved locally if force_new is false
         */
        template <bool ForceNew = false>
        [[nodiscard]] inline std::shared_ptr<Solver> tls_solver(const unsigned timeout = 0) {
            auto ret { get_tls_solver<ForceNew>() };
            if (timeout) {
                auto slv { *ret };
                if (slv->get_param_descrs().to_string().find("soft_timeout") != std::string::npos) {
                    slv->set("soft_timeout", timeout);
                    slv->set("solver2_timeout", timeout);
                }
                else {
                    slv->set("timeout", timeout);
                }
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
            return solver->check() == z3::check_result::sat;
        }

        /** Check to see if the solver is in a satisfiable state */
        inline bool satisfiable(Solver &solver,
                                const std::vector<Expr::RawPtr> &extra_constraints) {
            const ECHelper ec { *this, solver, extra_constraints };
            return satisfiable(solver);
        }

        /** Check if expr = sol is a solution to the given solver; none may be nullptr */
        inline bool solution(const Expr::RawPtr expr, const Expr::RawPtr sol, Solver &solver,
                             const std::vector<Expr::RawPtr> &extra_constraints) {
            ECHelper ec { *this, solver, extra_constraints, true };
            const auto eq { to_eq(expr, sol) }; // Debug verifies expr is not null
            solver->add(convert(eq.get()));
            return satisfiable(solver); // Debug verifies non-null
        }

        /** Check to see if sol is a solution to expr w.r.t the solver; neither may be nullptr */
        inline bool solution(const Expr::RawPtr expr, const Expr::RawPtr sol, Solver &solver) {
            const static thread_local std::vector<Expr::RawPtr> s {};
            return solution(expr, sol, solver, s);
        }

        /** Find the min value of expr that satisfies solver; returns an I64 or U64 */
        template <bool Signed> inline auto min(const Expr::RawPtr expr, Solver &solver) {
            return extrema<Signed, true>(expr, solver);
        }

        /** Find the min value of expr that satisfies solver; returns an I64 or U64 */
        template <bool Signed>
        inline auto min(const Expr::RawPtr expr, Solver &solver,
                        const std::vector<Expr::RawPtr> &extra_constraints) {
            const ECHelper ec { *this, solver, extra_constraints };
            return min<Signed>(expr, solver);
        }

        /** Find the max value of expr that satisfies solver; returns an I64 or U64 */
        template <bool Signed> inline auto max(const Expr::RawPtr expr, Solver &solver) {
            return extrema<Signed, false>(expr, solver);
        }

        /** Find the max value of expr that satisfies solver; returns an I64 or U64 */
        template <bool Signed>
        inline auto max(const Expr::RawPtr expr, Solver &solver,
                        const std::vector<Expr::RawPtr> &extra_constraints) {
            const ECHelper ec { *this, solver, extra_constraints };
            return max<Signed>(expr, solver);
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
                                             const U64 n_sol) {
            std::vector<Op::PrimVar> ret;
            ret.reserve(n_sol); // We do not resize as we may return < n_sol
            const z3::expr conv { convert(expr) };
            if (n_sol > 1) {
                solver->push();
            }
            // Repeat for each new solution
            for (U64 iter { 0 }; iter < n_sol; ++iter) {
                if (not satisfiable(solver)) {
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
        inline std::vector<Op::PrimVar> eval(const Expr::RawPtr expr, Solver &s, const U64 n,
                                             const std::vector<Expr::RawPtr> &extra_constraints) {
            const ECHelper ech { *this, s, extra_constraints };
            return eval(expr, s, n);
        }

        /** Evaluate every expr, return up to n different solutions
         *  No pointers may be nullptr
         */
        inline std::vector<std::vector<Op::PrimVar>>
        batch_eval(const std::vector<Expr::RawPtr> &exprs, Solver &s, const U64 n) {
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
            return batch_eval(converted, s, n);
        }

        /** Evaluate every expr, return up to n different solutions
         *  No pointers may be nullptr
         */
        inline std::vector<std::vector<Op::PrimVar>>
        batch_eval(const std::vector<Expr::RawPtr> &exprs, Solver &s, const U64 n,
                   const std::vector<Expr::RawPtr> &extra_constraints) {
            const ECHelper ech { *this, s, extra_constraints };
            return batch_eval(exprs, s, n);
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

        /** Return a tls solver
         *  Warning: solver is not saved locally if force_new is false
         */
        template <bool ForceNew> [[nodiscard]] inline std::shared_ptr<Solver> get_tls_solver() {
            if constexpr (ForceNew) {
                return std::make_shared<Solver>(z3::solver { tls.ctx });
            }
            else if (UNLIKELY(tls.solver == nullptr)) {
                tls.solver = std::make_shared<Solver>(z3::solver { tls.ctx });
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
                const std::set<Hash::Hash> tracked { get_tracked<true>(solver->assertions()) };
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
                    }
                }
            }
        }

        /** Return up to n_sol different solutions of solver given exprs, where exprs.size() > 1
         *  No pointers may be nullptr
         */
        inline std::vector<std::vector<Op::PrimVar>>
        batch_eval(const std::vector<z3::expr> exprs, Solver &solver, const U64 n_sol) const {
            UTIL_ASSERT(Util::Err::Usage, exprs.size() > 1,
                        "should only be called when exprs.size() > 1");
            // Prep
            solver->push();
            std::vector<std::vector<Op::PrimVar>> ret;
            ret.reserve(n_sol); // We do not resize as we may return < n_sol
            // Repeat for each new solution
            std::vector<z3::expr> z3_sol;
            for (U64 iter { 0 }; iter < n_sol; ++iter) {
                if (not satisfiable(solver)) {
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

        /** Coerce a PrimVar into a T via static_cast-ing
         *  This assumes the value of x will fit within T
         *  This assumes the PrimVar is set to a BV type
         */
        template <typename T> static T coerce_to(Op::PrimVar &&p) {
            using Usage = Util::Err::Usage;
            switch (p.index()) {
                /** A local macro used for consistency */
#define CASE_B(INDEX, TYPE)                                                                        \
    case INDEX: {                                                                                  \
        UTIL_VARIANT_VERIFY_INDEX_TYPE_IGNORE_CONST(p, INDEX, TYPE);                               \
        return static_cast<T>(std::get<TYPE>(p));                                                  \
    }
                CASE_B(5, uint8_t)
                CASE_B(6, uint16_t)
                CASE_B(7, uint32_t)
                CASE_B(8, U64)
#undef CASE_B
                case 9: {
                    UTIL_VARIANT_VERIFY_INDEX_TYPE_IGNORE_CONST(p, 9, BigInt);
                    const auto &bi = std::get<BigInt>(p);
                    UTIL_ASSERT(Usage, bi.bit_length < 64,
                                "Bit length of given PrimVar is too long");
                    return static_cast<T>(bi.value);
                }
                default:
                    UTIL_THROW(Usage, "Invalid PrimVar given");
            }
        }

        /** Create a == b; neither may be nullptr */
        static inline Expr::BasePtr to_eq(const Expr::RawPtr a_raw, const Expr::RawPtr b_raw) {
            UTIL_ASSERT_NOT_NULL_DEBUG(a_raw);
            UTIL_ASSERT_NOT_NULL_DEBUG(b_raw);
            return Create::eq(Expr::find(a_raw->hash), Expr::find(b_raw->hash));
        }

        /** Find the min/max value of expr that satisfies solver; returns an I64 or U64 */
        template <bool Signed, bool Minimize>
        inline auto extrema(const Expr::RawPtr raw_expr, Solver &solver) {
            // Check input
            using Usage = Util::Err::Usage;
            UTIL_ASSERT_NOT_NULL_DEBUG(raw_expr);
#ifdef DEBUG
            UTIL_ASSERT(Usage, CUID::is_t<Expr::BV>(raw_expr), "expr must be a BV");
#endif
            const auto len { Expr::get_bit_length(raw_expr) };
            UTIL_ASSERT(Usage, len <= 64, "ret cannot be called on BV wider than 64 bits");
            z3::expr expr { convert(raw_expr) };

            // Starting interval and comparators
            using Integer = std::conditional_t<Signed, I64, U64>;
            using Z3Integer = std::conditional_t<Signed, int64_t, uint64_t>;
/** A local macro for brevity */
#define MAX_S(S) ((Integer { 1 } << (len - S)) - 1 + (Integer { 1 } << (len - S)))
            Integer hi { Signed ? MAX_S(2) : MAX_S(1) };
            Integer lo { Signed ? (-hi - 1) : 0 };
#undef MAX_S

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
            bool pushed { false };
            while (hi > lo + 1) { // Difference of 1 instead of 0 to prevent infinite loop
                // Protect the current solver->ate
                if (not pushed) {
                    solver->push();
                    pushed = true;
                }
                // Add new bounding constraints
                const Integer middle { Util::avg(hi, lo) };
                solver->add(ge(expr, to_z3(Minimize ? lo : middle)));
                solver->add(le(expr, to_z3(Minimize ? middle : hi)));
                // Binary search
                const bool sat { satisfiable(solver) };
                (sat == Minimize ? hi : lo) = middle;
                // If the constraints need to be removed for the next step do so
                if (not sat) {
                    solver->pop();
                    pushed = false;
                }
            }

            // Last step of binary search
            if (not pushed) {
                solver->push();
            }
            solver->add(expr == to_z3(Minimize ? lo : hi));
            const Integer ret { Minimize == satisfiable(solver) ? lo : hi };
            solver->pop();
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
            inline ECHelper(Z3 &bk, Solver &s, const std::vector<Expr::RawPtr> &extra_constraints,
                            const bool force_push = false)
                : z3 { bk }, solver { s }, act { force_push || extra_constraints.size() > 0 } {
                if (act) {
                    solver->push();
                    for (auto &i : extra_constraints) {
                        solver->add(z3.convert(i));
                    }
                }
            }
            /** Destructor */
            inline ~ECHelper() {
                if (act) {
                    solver->pop();
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
            Solver &solver;
            /** True if extra_constraints is non-empty */
            bool act;
        };

        /** Holds and initalizes the thread_local z3 data */
        struct TLS final {

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
    };

} // namespace Backend::Z3

#endif
