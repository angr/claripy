/**
 * @file
 * @brief This file defines the Op class FP::ToBV
 */
#ifndef R_OP_FP_TOBV_HPP_
#define R_OP_FP_TOBV_HPP_

#include "../../mode.hpp"
#include "../base.hpp"


namespace Op::FP {

    /** The op class: to_bv */
    template <bool Signed> class ToBV final : public Base {
        OP_FINAL_INIT(ToBV, Signed, "FP::");

      public:
        /** The FP mode */
        const Mode::FP::Rounding mode;
        /** The fp to convert: This must be an Expr::BV pointer
         *  Note: We leave it as a base for optimizations purposes
         */
        const Expr::BasePtr fp;

        /** Python's repr function (outputs json) */
        inline void repr(std::ostream &out, const bool verbose = false) const override final {
            out << R"|({ "name":")|" << op_name() << R"|(", "signed":)|" << std::boolalpha << Signed
                << R"|(, "mode":)|" << Util::to_underlying(mode) << R"|(, "fp":)|";
            Expr::repr(fp, out, verbose);
            out << " }";
        }

        /** Adds the raw expr children of the expr to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        inline void unsafe_add_reversed_children(Stack &s) const override final {
            s.emplace(fp.get());
        }

      private:
        /** Protected constructor
         *  Ensure that fp is an FP
         */
        explicit inline ToBV(const Hash::Hash &h, const Mode::FP::Rounding m,
                             const Expr::BasePtr &f)
            : Base { h, static_cuid }, mode { m }, fp { f } {
            Util::affirm<Error::Expr::Type>(CUID::is_t<Expr::FP>(fp),
                                            WHOAMI "Operand fp must be an Expr::FP");
        }
    };

} // namespace Op::FP

#endif
