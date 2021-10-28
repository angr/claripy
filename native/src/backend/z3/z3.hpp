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
        static UTILS_CCBOOL apply_annotations = false;

        /** Constructor */
        inline Z3() noexcept = default;
        /** Destructor */
        inline ~Z3() noexcept = default;

        /********************************************************************/
        /*                        Function Overrides                        */
        /********************************************************************/

        /** Clears translocation data */
        inline void clear_persistent_data() override final {
            Util::Log::warning("Z3 backend clearing persistent data...");
            tls.symbol_annotation_translocation_data.clear();
        }

        /** The name of this backend */
        [[nodiscard]] inline const char *name() const noexcept override final { return "z3"; }

        /** Simplify the given expr
         *  expr may not be nullptr
         */
        inline Expr::BasePtr simplify(const Expr::RawPtr expr) override final {
            UTILS_AFFIRM_NOT_NULL_DEBUG(expr);
            namespace Ex = Expr;
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
                    Util::Log::info("Z3 Backend will not simplify expr with CUID: ", expr->cuid);
#ifdef DEBUG
                    auto ret { Ex::find(expr->hash) };
                    Util::affirm<Util::Err::HashCollision>(ret.get() == expr, WHOAMI);
                    return ret;
#else
                    return Ex::find(expr->hash);
#endif
                }
            }
        }

      public:
        /********************************************************************/
        /*                         Member Functions                         */
        /********************************************************************/

        /** Return a tls solver
         *  If timeout is not 0, timeouts will be configured for the solver
         *  Warning: solver is not saved locally if force_new is false
         */
        template <bool ForceNew = false>
        [[nodiscard]] inline std::shared_ptr<z3::solver> tls_solver(const unsigned timeout = 0) {
            auto ret { get_tls_solver<ForceNew>() };
            if (timeout != 0) {
                if (ret->get_param_descrs().to_string().find("soft_timeout") != std::string::npos) {
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
        template <bool Track = false> void add(z3::solver &solver, const Expr::RawPtr constraint) {
            const Expr::RawPtr arr[] { constraint };
            add_helper<Track>(solver, arr, 1);
        }

        /** Add constraints to the solver, track if Track */
        template <bool Track = false>
        void add(z3::solver &solver, const std::vector<Expr::RawPtr> &constraints) {
            add_helper<Track>(solver, constraints.data(), constraints.size());
        }

        /** Check to see if the solver is in a satisfiable state */
        inline bool satisfiable(z3::solver &solver) {
            return solver.check() == z3::check_result::sat;
        }

        /** Check to see if the solver is in a satisfiable state */
        inline bool satisfiable(z3::solver &solver,
                                const std::vector<Expr::RawPtr> &extra_constraints) {
            const ECHelper ec { *this, solver, extra_constraints };
            return satisfiable(solver);
        }

        /** Check if expr = sol is a solution to the given solver; none may be nullptr */
        inline bool solution(const Expr::RawPtr expr, const Expr::RawPtr sol, z3::solver &solver,
                             const std::vector<Expr::RawPtr> &extra_constraints) {
            ECHelper ec { *this, solver, extra_constraints, true };
            const auto eq { to_eq(expr, sol) }; // Debug verifies expr is not null
            solver.add(convert(eq.get()));
            return satisfiable(solver, extra_constraints); // Debug verifies non-null
        }

        /** Check to see if sol is a solution to expr w.r.t the solver; neither may be nullptr */
        inline bool solution(const Expr::RawPtr expr, const Expr::RawPtr sol, z3::solver &solver) {
            const static thread_local std::vector<Expr::RawPtr> s {};
            return solution(expr, sol, solver, s);
        }

        /** Find the min value of expr that satisfies solver; returns an int64_t or uint64_t */
        template <bool Signed> inline auto min(const Expr::RawPtr expr, z3::solver &solver) {
            return extrema<Signed, true>(expr, solver);
        }

        /** Find the min value of expr that satisfies solver; returns an int64_t or uint64_t */
        template <bool Signed>
        inline auto min(const Expr::RawPtr expr, z3::solver &solver,
                        const std::vector<Expr::RawPtr> &extra_constraints) {
            const ECHelper ec { *this, solver, extra_constraints };
            return min<Signed>(expr, solver);
        }

        /** Find the max value of expr that satisfies solver; returns an int64_t or uint64_t */
        template <bool Signed> inline auto max(const Expr::RawPtr expr, z3::solver &solver) {
            return extrema<Signed, false>(expr, solver);
        }

        /** Find the max value of expr that satisfies solver; returns an int64_t or uint64_t */
        template <bool Signed>
        inline auto max(const Expr::RawPtr expr, z3::solver &solver,
                        const std::vector<Expr::RawPtr> &extra_constraints) {
            const ECHelper ec { *this, solver, extra_constraints };
            return max<Signed>(expr, solver);
        }

        /** Return the unsat core from the solver
         *  Warning: This assumes all of solver's assertions were added by add<true>
         */
        inline std::vector<Expr::BasePtr> unsat_core(z3::solver &solver) {
            std::vector<Expr::BasePtr> ret;
            const auto cores { solver.unsat_core() };
            const auto len { cores.size() };
            ret.reserve(len);
            z3::expr_vector assertions { solver.ctx() };
            std::map<Hash::Hash, const int> indexes;
            for (unsigned i { 0 }; i < len; ++i) {
                const auto child { cores[static_cast<int>(i)] };
                const Hash::Hash h { extract_hash(child) };
                // First try to lookup the child by the hash
                if (auto lookup { Expr::find(h) }; lookup != nullptr) {
                    Util::Log::info(__LINE__);
                    ret.emplace_back(std::move(lookup));
                    continue;
                }
                // Otherwise, abstract assertion object
                if (assertions.size() == 0) {
                    assertions = solver.assertions();
                    const auto len_a { assertions.size() };
                    for (int k = 0; k < static_cast<int>(len_a); ++k) {
                        Util::map_emplace(indexes, extract_hash(assertions[k]), k);
                    }
                }
                ret.emplace_back(abstract(assertions[indexes[h]]));
            }
            return ret;
        }

        /** Evaluate expr, return n different solutions
         *  No pointers may be nullptr
         */
        inline std::vector<PrimVar> eval(const Expr::RawPtr expr, z3::solver &solver,
                                         const UInt n_sol) {
            std::vector<PrimVar> ret;
            ret.reserve(n_sol); // We do not resize as we may return < n_sol
            const z3::expr conv { convert(expr) };
            if (n_sol > 1) {
                solver.push();
            }
            // Repeat for each new solution
            for (UInt iter { 0 }; iter < n_sol; ++iter) {
                if (!satisfiable(solver)) {
                    // No point in search further, return what we have
                    break;
                }
                // Extract solutions
                const z3::model model { solver.get_model() };
                const auto evaled { model.eval(conv, true) };
                ret.emplace_back(abstract_to_prim(evaled));
                // Construct extra constraints to prevent solution duplication
                if (iter + 1 != n_sol) {
                    solver.add(conv != evaled);
                }
            }
            if (n_sol > 1) {
                solver.pop();
            }
            return ret;
        }

        /** Evaluate expr, return n different solutions
         *  No pointers may be nullptr
         */
        inline std::vector<PrimVar> eval(const Expr::RawPtr expr, z3::solver &s, const UInt n,
                                         const std::vector<Expr::RawPtr> &extra_constraints) {
            const ECHelper ech { *this, s, extra_constraints };
            return eval(expr, s, n);
        }

        /** Evaluate every expr, return n different solutions
         *  No pointers may be nullptr
         */
        inline std::vector<std::vector<PrimVar>> batch_eval(const std::vector<Expr::RawPtr> &exprs,
                                                            z3::solver &s, const UInt n) {
            if (UNLIKELY(exprs.size() == 0)) {
                return {};
            }
            if (UNLIKELY(exprs.size() == 1)) { // Why we prefer eval to batch
                Util::Log::info(WHOAMI
                                "called on exprs of size 1; eval is more efficient for this");
                const auto sols { eval(exprs[0], s, n) };
                std::vector<std::vector<PrimVar>> ret;
                ret.reserve(sols.size());
                for (const auto &i : sols) {
                    ret.emplace_back(std::vector<PrimVar> { i }); // Why we prefer eval to batch
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

        /** Evaluate every expr, return n different solutions
         *  No pointers may be nullptr
         */
        inline std::vector<std::vector<PrimVar>>
        batch_eval(const std::vector<Expr::RawPtr> &exprs, z3::solver &s, const UInt n,
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
                                            std::vector<const z3::expr *> &args) override final {
            return Dispatch<Z3>::dispatch_conversion(
                expr, args, tls.symbol_annotation_translocation_data, *this);
        }

        /** Abstract a backend object into a claricpp expr */
        inline AbstractionVariant
        dispatch_abstraction(const z3::expr &b_obj,
                             std::vector<AbstractionVariant> &args) override final {
            return Dispatch<Z3>::dispatch_abstraction(
                b_obj, args, tls.symbol_annotation_translocation_data, *this);
        }

        /********************************************************************/
        /*                     Private Helper Functions                     */
        /********************************************************************/

        /** Return a tls solver
         *  Warning: solver is not saved locally if force_new is false
         */
        template <bool ForceNew> [[nodiscard]] inline std::shared_ptr<z3::solver> get_tls_solver() {
            if constexpr (ForceNew) {
                return std::make_shared<z3::solver>(tls.ctx);
            }
            else if (UNLIKELY(tls.solver == nullptr)) {
                tls.solver = std::make_shared<z3::solver>(tls.ctx);
            }
            return tls.solver;
        }

        /** Extracts the hash from the boolean z3::expr expr named: |X|
         *  X is a string output by Util::to_hex
         *  Warning if X is not an output of Util::to_hex, an invalid result is returned
         */
        inline Hash::Hash extract_hash(const z3::expr &expr) {
            // Note that we use the lower level API to avoid a string allocation fpr speed
            const char *str { Z3_ast_to_string(expr.ctx(), expr) + 3 }; // Remove prefix |0x
            Hash::Hash ret { 0 };
            while (str[1] != '\0') { // We want to stop one char short to skip the last '|'
                ret <<= 4;
                ret += Util::hex_to_num(str[0]);
                str += 1;
            }
            return ret;
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
                const auto bool_name { assertions[Util::sign(i)].arg(0) };
#ifdef DEBUG
                const auto [_, success] { tracked.emplace(extract_hash(bool_name)) };
                Util::affirm<Util::Err::HashCollision>(success, WHOAMI "Hash collision");
                (void) _;
#else
                tracked.emplace(extract_hash(bool_name));
#endif
            }
            return tracked;
        }

        /** Add constraints to the solver, track if Track */
        template <bool Track>
        void add_helper(z3::solver &solver, CTSC<Expr::RawPtr> constraints, const UInt c_len) {
            if constexpr (!Track) {
                for (UInt i { 0 }; i < c_len; ++i) {
                    solver.add(convert(constraints[i]));
                }
            }
            else {
                const std::set<Hash::Hash> tracked { get_tracked(solver) };
                char buf[Util::to_hex_max_len<Hash::Hash>];
                for (UInt i { 0 }; i < c_len; ++i) {
                    // If the new constraint is not track, track it
                    const Hash::Hash c_hash { constraints[i]->hash };
                    if (const auto lookup { tracked.find(c_hash) }; lookup == tracked.end()) {
                        // We use to_hex to avoid heap allocations due to temporary strings
                        // This also leads to avoiding much the same when converting back
                        (void) Util::to_hex(c_hash, buf); // Populates buf
                        solver.add(convert(constraints[i]), solver.ctx().bool_const(buf));
                    }
                }
            }
        }

        /** Return up to n_sol different solutions of solver given exprs, where exprs.size() > 1
         *  No pointers may be nullptr
         */
        inline std::vector<std::vector<PrimVar>> batch_eval(const std::vector<z3::expr> exprs,
                                                            z3::solver &solver, const UInt n_sol) {
            Util::affirm<Util::Err::Usage>(exprs.size() > 1,
                                           WHOAMI "should only be called when exprs.size() > 1");
            // Prep
            solver.push();
            std::vector<std::vector<PrimVar>> ret;
            ret.reserve(n_sol); // We do not resize as we may return < n_sol
            // Repeat for each new solution
            std::vector<z3::expr> z3_sol;
            for (UInt iter { 0 }; iter < n_sol; ++iter) {
                if (!satisfiable(solver)) {
                    // No point in search further, return what we have
                    break;
                }

                // Prep loop body
                if (iter != 0) {
                    z3_sol.clear();
                }
                z3_sol.reserve(exprs.size());
                ret.emplace_back(); // Create a new vector

                // Extract solutions
                const z3::model model { solver.get_model() };
                for (const auto &expr : exprs) {
                    z3_sol.emplace_back(model.eval(expr, true));
                    ret[iter].emplace_back(abstract_to_prim(z3_sol.back()));
                }

                // Construct extra constraints to prevent solution duplication
                if (iter + 1 != n_sol) {
                    z3::expr current_sol { exprs[0] == z3_sol[0] };
                    for (UInt i { 1 }; i < exprs.size(); ++i) {
                        current_sol = current_sol && (exprs[i] == z3_sol[i]);
                    }
                    solver.add(!current_sol);
                }
            }
            // Cleanup
            solver.pop();
            return ret;
        }

        /** The method used to simplify z3 boolean exprs*/
        inline z3::expr bool_simplify(const z3::expr &expr) { return tls.bt(expr); }

        /** Abstract b_obj to a type in PrimVar */
        inline PrimVar abstract_to_prim(const z3::expr &b_obj) {
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
            return Dispatch<Z3>::dispatch_abstraction_to_prim(b_obj, *this);
#endif
        }

        /** Coerce a PrimVar into a T via static_cast-ing
         *  This assumes the value of x will fit within T
         *  This assumes the PrimVar is set to a BV type
         */
        template <typename T> T coerce_to(PrimVar &&p) {
            using Usage = Util::Err::Usage;
            switch (p.index()) {
                /** A local macro used for consistency */
#define CASE_B(INDEX, TYPE)                                                                        \
    case INDEX: {                                                                                  \
        UTILS_VARIANT_VERIFY_INDEX_TYPE_IGNORE_CONST(p, INDEX, TYPE);                              \
        return static_cast<T>(std::get<TYPE>(p));                                                  \
    }
                CASE_B(5, uint8_t)
                CASE_B(6, uint16_t)
                CASE_B(7, uint32_t)
                CASE_B(8, uint64_t)
#undef CASE_B
                case 9: {
                    UTILS_VARIANT_VERIFY_INDEX_TYPE_IGNORE_CONST(p, 9, BigInt);
                    const auto &bi = std::get<BigInt>(p);
                    Util::affirm<Usage>(bi.bit_length < 64,
                                        WHOAMI "Bit length of given PrimVar is too long");
                    return static_cast<T>(bi.value);
                }
                default:
                    throw Usage(WHOAMI "Invalid PrimVar given");
            }
        }

        /** Create a == b; neither may be nullptr */
        static inline Expr::BasePtr to_eq(const Expr::RawPtr a_raw, const Expr::RawPtr b_raw) {
            UTILS_AFFIRM_NOT_NULL_DEBUG(a_raw);
            UTILS_AFFIRM_NOT_NULL_DEBUG(b_raw);
            return Create::eq(Expr::find(a_raw->hash), Expr::find(b_raw->hash));
        }

        /** Find the min/max value of expr that satisfies solver; returns an int64_t or uint64_t */
        template <bool Signed, bool Minimize>
        inline auto extrema(const Expr::RawPtr raw_expr, z3::solver &solver) {
            // Check input
            using Usage = Util::Err::Usage;
            UTILS_AFFIRM_NOT_NULL_DEBUG(raw_expr);
#ifdef DEBUG
            Util::affirm<Usage>(CUID::is_t<Expr::BV>(raw_expr), WHOAMI "expr must be a BV");
#endif
            const auto len { Expr::get_bit_length(raw_expr) };
            Util::affirm<Usage>(len <= 64, WHOAMI "ret cannot be called on BV wider than 64 bits");
            z3::expr expr { convert(raw_expr) };

            // Starting interval and comparators
            using Integer = std::conditional_t<Signed, int64_t, uint64_t>;
/** A local macro for brevity */
#define MAX_S(S) ((Integer { 1 } << (len - S)) - 1 + (Integer { 1 } << (len - S)))
            Integer hi { Signed ? MAX_S(2) : MAX_S(1) };
            Integer lo { Signed ? (-hi - 1) : 0 };
#undef MAX_S

            // Inline-able lambdas to for clarity
            const auto to_z3 { [&len](const Integer i) {
                return tls.ctx.bv_val(i, Util::narrow<unsigned>(len));
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
                // Protect the current solver state
                if (!pushed) {
                    solver.push();
                    pushed = true;
                }
                // Add new bounding constraints
                const Integer middle { Util::avg(hi, lo) };
                solver.add(ge(expr, to_z3(Minimize ? lo : middle)));
                solver.add(le(expr, to_z3(Minimize ? middle : hi)));
                // Binary search
                const bool sat { satisfiable(solver) };
                (sat == Minimize ? hi : lo) = middle;
                // If the constraints need to be removed for the next step do so
                if (!sat) {
                    solver.pop();
                    pushed = false;
                }
            }

            // Last step of binary search
            if (!pushed) {
                solver.push();
            }
            solver.add(expr == to_z3(Minimize ? lo : hi));
            const Integer ret { Minimize == satisfiable(solver) ? lo : hi };
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
                            const std::vector<Expr::RawPtr> &extra_constraints,
                            const bool force_push = false)
                : z3 { bk }, solver { s }, act { force_push || extra_constraints.size() > 0 } {
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

        /** Holds and initalizes the thread_local z3 data */
        struct TLS final {

            /** The z3 context this uses */
            z3::context ctx {};
            /** The BoolTactic the z3 backend will use */
            BoolTactic bt { ctx };
            /** The z3 solver to be used by this backend */
            std::shared_ptr<z3::solver> solver { nullptr };

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
