/**
 * @file
 * @brief This file defines the Op class FP::FPToFP
 */
#ifndef R_OP_FP_FPTOFP_HPP_
#define R_OP_FP_FPTOFP_HPP_

#include "../../mode.hpp"
#include "../base.hpp"


namespace Op::FP {

    /** The op class: fp_to_fp */
    template <typename T, bool Signed> class FPToFP final : public Base {
        OP_FINAL_INIT(FPToFP, Signed, "FP::");

      public:
        /** The FP mode */
        const Mode::FP::Rounding mode;
        /** The expression to convert */
        const Expression::BasePtr fp;
        /** The fp width to convert to */
        const Mode::FP::Width width;

        /** Python's repr function (outputs json) */
        inline void repr(std::ostringstream &out,
                         const bool verbose = false) const override final {
            out << R"|({ "name":")|" << op_name() << R"|(", "signed":)|" << std::boolalpha
                << Signed << R"|(, "rounding mode":)|" << Utils::to_underlying(mode)
                << R"|(, "fp":)|";
            Expression::repr(fp, out, verbose);
            out << R"|(, "width":)|" << width << " }";
        }

        /** Add's the raw expression children of the expression to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        inline void add_reversed_children(Stack &s) const override final { s.emplace(fp.get()); }

      private:
        /** Protected constructor
         *  Ensure that fp is an FP
         */
        explicit inline FPToFP(const Hash::Hash &h, const Mode::FP::Rounding m,
                               const Expression::BasePtr &f, const Mode::FP::Width w)
            : Base { h, static_cuid }, mode { m }, fp { f }, width { w } {}
    };

} // namespace Op::FP

#endif
