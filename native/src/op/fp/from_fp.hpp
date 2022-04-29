/**
 * @file
 * @brief This file defines the Op class FP::FromFP
 */
#ifndef R_SRC_OP_FP_FROMFP_HPP_
#define R_SRC_OP_FP_FROMFP_HPP_

#include "../../mode.hpp"
#include "../base.hpp"


namespace Op::FP {

    /** The op class which converts an FP into another FP (for example, a float into a double) */
    class FromFP final : public Base {
        OP_FINAL_INIT(FromFP, "FP::", 0);

      public:
        /** The FP mode */
        const Mode::FP::Rounding mode;
        /** The expr to convert */
        const Expr::BasePtr fp;
        /** The fp width to convert to */
        const Mode::FP::Width width;

        /** repr */
        inline void repr_stream(std::ostream &out) const final {
            out << R"|({ "name":")|" << op_name() << R"|(, "rounding mode":)|"
                << Util::to_underlying(mode) << R"|(, "fp":)|";
            fp->repr_stream(out);
            out << R"|(, "width":)|" << width << " }";
        }

        /** Appends the expr children of the expr to the given vector
         *  Note: This should only be used when returning children to python
         */
        inline std::vector<ArgVar> python_children() const final { return { mode, fp, width }; }

      private:
        /** Private constructor
         *  Ensure that fp is an FP
         */
        explicit inline FromFP(const Hash::Hash &h, const Mode::FP::Rounding m,
                               const Expr::BasePtr &f, const Mode::FP::Width w)
            : Base { h, static_cuid }, mode { m }, fp { f }, width { w } {
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
