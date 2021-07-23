/**
 * @file
 * @brief This file defines the Op class FP::FromNot2sComplementBV
 */
#ifndef R_OP_FP_FROMNOT2SCOMPEIMENTBV_HPP_
#define R_OP_FP_FROMNOT2SCOMPEIMENTBV_HPP_

#include "../../mode.hpp"
#include "../base.hpp"


namespace Op::FP {

    /** The op class which converts a non-2s-complement BV into an FP */
    class FromNot2sComplementBV final : public Base {
        OP_FINAL_INIT(FromNot2sComplementBV, 0, "FP::");

      public:
        /** The expression to convert */
        const Expression::BasePtr bv;
        /** The fp width to convert to */
        const Mode::FP::Width width;

        /** Python's repr function (outputs json) */
        inline void repr(std::ostream &out, const bool verbose = false) const override final {
            out << R"|({ "name":")|" << op_name() << R"|(, "bv":)|";
            Expression::repr(bv, out, verbose);
            out << R"|(, "width":)|" << width << " }";
        }

        /** Adds the raw expression children of the expression to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        inline void add_reversed_children(Stack &s) const override final { s.emplace(bv.get()); }

      private:
        /** Protected constructor
         *  Ensure that bv is a BV
         */
        explicit inline FromNot2sComplementBV(const Hash::Hash &h, const Expression::BasePtr &b,
                                              const Mode::FP::Width w)
            : Base { h, static_cuid }, bv { b }, width { w } {}
    };

} // namespace Op::FP

#endif
