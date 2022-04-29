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
    class ToBV : public Base {
        OP_PURE_INIT(ToBV);

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

      protected:
        /** Protected constructor
         *  Ensure that fp is an FP
         */
        explicit inline ToBV(const Hash::Hash &h, const CUID::CUID &cuid_,
                             const Mode::FP::Rounding m, const Expr::BasePtr &f)
            : Base { h, cuid_ }, mode { m }, fp { f } {
            UTIL_ASSERT(Error::Expr::Type, CUID::is_t<Expr::FP>(fp),
                        "Operand fp must be an Expr::FP");
        }

      private:
        /** Adds the raw expr children of the expr to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        inline void unsafe_add_reversed_children(Stack &s) const final { s.emplace(fp.get()); }
    };

    /** Signed ToBV */
    class ToBVSigned final : public ToBV {
        OP_FINAL_INIT(ToBVSigned, "FP::");

      private:
        /** Private constructor */
        explicit inline ToBVSigned(const Hash::Hash &h, const Mode::FP::Rounding m,
                                   const Expr::BasePtr &f)
            : ToBV { h, static_cuid, m, f } {}
    };

    /** Default virtual dtor */
    inline ToBV::~ToBV() noexcept = default;

    /** Unsigned ToBV */
    class ToBVUnsigned final : public ToBV {
        OP_FINAL_INIT(ToBVUnsigned, "FP::");

      private:
        /** Private constructor */
        explicit inline ToBVUnsigned(const Hash::Hash &h, const Mode::FP::Rounding m,
                                     const Expr::BasePtr &f)
            : ToBV { h, static_cuid, m, f } {}
    };
} // namespace Op::FP

#endif
