/**
 * @file
 * @brief This file defines a z3 solver wrapper
 */
#ifndef R_SRC_BACKEND_Z3_SOLVER_HPP_
#define R_SRC_BACKEND_Z3_SOLVER_HPP_

#include <z3++.h>


namespace Backend::Z3 {
    /** A Z3 Solver object */
    class Solver final {
      public:
        /** Constructor */
        inline Solver(z3::solver sol) : s { std::move(sol) } {}
        /** Allow access to the z3::solver */
        inline z3::solver *operator->() { return &s; }
        /** Allow const access to the z3::solver */
        inline const z3::solver *operator->() const { return &s; }
        // Friend operators
        friend inline std::ostream &operator<<(std::ostream &, const Solver &);
        /** Clone the solver */
        inline Solver clone(z3::context & c) const {
            return z3::solver(c, s, z3::solver::translate{});
        }
      private:
        /** The z3::solver */
        z3::solver s;
    };

    /** Stream operator */
    inline std::ostream &operator<<(std::ostream &os, const Solver &s) {
        return os << s.s;
    }

} // namespace Backend::Z3


#endif
