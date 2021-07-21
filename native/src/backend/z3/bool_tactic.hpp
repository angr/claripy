/**
 * @file
 * @brief This file defines the tactics used to simplify z3 bools
 */
#ifndef R_BACKEND_Z3_BOOLTACTIC_HPP_
#define R_BACKEND_Z3_BOOLTACTIC_HPP_

#include "tl_ctx.hpp"

#include "../../utils.hpp"
namespace Backend::Z3 {

    /** This class defines tactics used to simplify z3 bools */
    class BoolTactic {
      public:
        /** Run the tactics on the given z3::expr */
        z3::expr operator()(const z3::expr &in) {
            auto in2 = in.simplify();
            z3::goal goal { Private::tl_ctx };
            goal.add(in2);
            const auto ar { tactics.apply(goal) };
            return to_expr(ar);
        }

      private:
        /** The tactics contained by this class */
        z3::tactic tactics { mk_tactics() };

        /** Used to create the tactics contained by this class */
        static inline z3::tactic mk_tactics() {
            return z3::tactic(Private::tl_ctx, "simplify") &
                   z3::tactic(Private::tl_ctx, "propagate-ineqs") &
                   z3::tactic(Private::tl_ctx, "propagate-values") &
                   z3::tactic(Private::tl_ctx, "unit-subsume-simplify") &
                   z3::tactic(Private::tl_ctx, "aig");
        }

        /** Convert a z3::apply_result a z3::expr */
        static inline z3::expr to_expr(const z3::apply_result &ar) {
            const auto len { ar.size() };
            switch (len) {
                case 0:
                    return Private::tl_ctx.bool_val(false);
                case 1:
                    return ar[0].as_expr();
                // len > 1; or each goal as expressions
                default: {
                    z3::expr ret { ar[0].as_expr() };
                    for (int i = 0; i < static_cast<int>(len); ++i) {
                        ret = ret || ar[i].as_expr();
                    }
                    return ret;
                }
            };
        }
    };

} // namespace Backend::Z3

#endif
