/**
 * @file
 * @brief This file defines the tactics used to simplify z3 bools
 */
#ifndef R_SRC_BACKEND_Z3_BOOLTACTIC_HPP_
#define R_SRC_BACKEND_Z3_BOOLTACTIC_HPP_

#include <z3++.h>


namespace Backend::Z3 {

    /** This class defines tactics used to simplify z3 bools */
    class BoolTactic {
      public:
        /** Constructor */
        inline BoolTactic(z3::context &c) : ctx { c }, tactics { mk_tactics(c) } {}
        /** Run the tactics on the given z3::expr */
        z3::expr operator()(const z3::expr &in) {
            z3::goal goal { ctx };
            goal.add(in);
            const auto ar { tactics.apply(goal) };
            return to_expr(ar);
        }

      private:
        /** Used to create the tactics contained by this class */
        static inline z3::tactic mk_tactics(z3::context &c) {
            return z3::tactic(c, "simplify") & z3::tactic(c, "propagate-ineqs") &
                   z3::tactic(c, "propagate-values") & z3::tactic(c, "unit-subsume-simplify") &
                   z3::tactic(c, "aig");
        }
        /** Convert a z3::apply_result a z3::expr */
        inline z3::expr to_expr(const z3::apply_result &ar) {
            const auto len { ar.size() };
            switch (len) {
                case 0:
                    return ctx.bool_val(false);
                case 1:
                    return ar[0].as_expr();
                // len > 1; or each goal as exprs
                default: {
                    z3::expr ret { ar[0].as_expr() };
                    for (int i = 0; i < static_cast<int>(len); ++i) {
                        ret = ret || ar[i].as_expr();
                    }
                    return ret;
                }
            };
        }

        /** The z3 context to use */
        z3::context &ctx;
        /** The tactics contained by this class */
        z3::tactic tactics;
    };

} // namespace Backend::Z3

#endif
