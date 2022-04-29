/**
 * @file
 * @brief This file defines the Op class FP::ToBV
 */
#ifndef R_SRC_OP_FP_TOBV_HPP_
#define R_SRC_OP_FP_TOBV_HPP_

#include "../../mode.hpp"
#include "../base.hpp"


namespace Op::FP {

    /** The op class: to_bv */
    template <Mode::Signed Sgn> class ToBV final : public Base {
        OP_FINAL_INIT(ToBV, "FP::", Sgn);

      public:
        /** The FP mode */
        const Mode::FP::Rounding mode;
        /** The fp to convert: This must be an Expr::BV pointer
         *  Note: We leave it as a base for optimizations purposes
         */
        const Expr::BasePtr fp;

        /** repr */
        inline void repr_stream(std::ostream &out) const final {
            out << R"|({ "name":")|" << op_name() << R"|(, "mode":)|" << Util::to_underlying(mode)
                << R"|(, "fp":)|";
            fp->repr_stream(out);
            out << " }";
        }

        /** Appends the expr children of the expr to the given vector
         *  Note: This should only be used when returning children to python
         */
        inline std::vector<ArgVar> python_children() const final { return { mode, fp }; }

      private:
        /** Private constructor
         *  Ensure that fp is an FP
         */
        explicit inline ToBV(const Hash::Hash &h, const Mode::FP::Rounding m,
                             const Expr::BasePtr &f)
            : Base { h, static_cuid }, mode { m }, fp { f } {
            UTIL_ASSERT(Error::Expr::Type, CUID::is_t<Expr::FP>(fp),
                        "Operand fp must be an Expr::FP");
        }

        /** Adds the raw expr children of the expr to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        inline void unsafe_add_reversed_children(Stack &s) const final { s.emplace(fp.get()); }
    };

} // namespace Op::FP

#endif
