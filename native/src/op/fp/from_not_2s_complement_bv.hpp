/**
 * @file
 * @brief This file defines the Op class FP::FromNot2sComplementBV
 */
#ifndef R_SRC_OP_FP_FROMNOT2SCOMPLEMENTBV_HPP_
#define R_SRC_OP_FP_FROMNOT2SCOMPLEMENTBV_HPP_

#include "../../mode.hpp"
#include "../base.hpp"


namespace Op::FP {

    /** The op class which converts a non-2s-complement BV into an FP */
    class FromNot2sComplementBV final : public Base {
        OP_FINAL_INIT(FromNot2sComplementBV, "FP::", 0);

      public:
        /** The expr to convert */
        const Expr::BasePtr bv;
        /** The fp width to convert to */
        const Mode::FP::Width width;

        /** repr */
        inline void repr_stream(std::ostream &out) const final {
            out << R"|({ "name":")|" << op_name() << R"|(, "bv":)|";
            bv->repr_stream(out);
            out << R"|(, "width":)|" << width << " }";
        }

        /** Appends the expr children of the expr to the given vector
         *  Note: This should only be used when returning children to python
         */
        inline std::vector<ArgVar> python_children() const final { return { bv, width }; }

      private:
        /** Private constructor
         *  Ensure that bv is a BV
         */
        explicit inline FromNot2sComplementBV(const Hash::Hash &h, const Expr::BasePtr &b,
                                              const Mode::FP::Width w)
            : Base { h, static_cuid }, bv { b }, width { w } {
            UTIL_ASSERT(Error::Expr::Type, CUID::is_t<Expr::BV>(b),
                        "Operand b must be an Expr::BV");
        }

        /** Adds the raw expr children of the expr to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        inline void unsafe_add_reversed_children(Stack &s) const final { s.emplace(bv.get()); }
    };

} // namespace Op::FP

#endif
