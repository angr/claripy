#ifndef R_BACKEND_Z3_SOLVER_HPP_
#define R_BACKEND_Z3_SOLVER_HPP_

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

      private:
        /** The z3::solver */
        z3::solver s;
    };
} // namespace Backend::Z3


#endif
