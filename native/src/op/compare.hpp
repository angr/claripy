/**
 * @file
 * @brief This file defines the generic Compare Op class
 */
#ifndef R_OP_COMPARE_HPP_
#define R_OP_COMPARE_HPP_

#include "binary.hpp"


namespace Op {

    /** The binary comparison op class(es): ULT, SLT, UGT, SGT, ULE, SLE, UGE, SGE
     *  Requires equal sized inputs
     */
    template <Mode::Compare Mask> class Compare final : public Binary<true> {
        OP_FINAL_INIT(Compare, Util::to_underlying(Mask), "");

      private:
        /** Private constructor */
        explicit inline Compare(const ::Hash::Hash &h, const ::Expr::BasePtr &l,
                                const ::Expr::BasePtr &r)
            : Binary { h, static_cuid, l, r } {}

        /** Python's repr function (outputs json) */
        inline void repr(std::ostream &out, const bool verbose = false) const override final {
            repr_helper(out, verbose);
            out << R"|(, "extra":")|" << Mask << "\" }";
        }
    };

} // namespace Op

#endif
