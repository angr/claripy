/**
 * @file
 * @brief An op that takes in one Expr and one integer
 */
#ifndef R_OP_UINTBINARY_HPP_
#define R_OP_UINTBINARY_HPP_

#include "base.hpp"

#include "../error.hpp"

#include <type_traits>


/** A macro used to define a trivial subclass of Binary
 *  PREFIX and TARG are passed to OP_FINAL_INIT
 */
#define OP_UINTBINARY_TRIVIAL_SUBCLASS(CLASS, PREFIX, TARG)                                        \
    class CLASS final : public ::Op::UIntBinary {                                                  \
        OP_FINAL_INIT(CLASS, PREFIX, TARG);                                                        \
                                                                                                   \
      private:                                                                                     \
        /** Private constructor */                                                                 \
        explicit inline CLASS(const ::Hash::Hash &h, const ::Expr::BasePtr &e, const UInt i)       \
            : UIntBinary { h, static_cuid, e, i } {}                                               \
    };


namespace Op {

    /** An Op class that has an Expr operand and an int operand */
    class UIntBinary : public Base {
        OP_PURE_INIT(UIntBinary);

      public:
        /** Expr operand */
        const Expr::BasePtr expr;
        /* Integer operand */
        const UInt integer;

        /** Python's repr function (outputs json) */
        inline void repr(std::ostream &out) const final {
            out << R"|({ "name":")|" << op_name() << R"|(", "expr":)|";
            expr->repr(out);
            out << R"|(, "integer":)|" << integer << " }";
        }

        /** Adds the raw expr children of the expr to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        inline void unsafe_add_reversed_children(Stack &s) const final { s.emplace(expr.get()); }

        /** Appends the expr children of the expr to the given vector
         *  Note: This should only be used when returning children to python
         */
        inline void python_children(std::vector<ArgVar> &v) const final {
            v.emplace_back(expr);
            v.emplace_back(integer);
        }

      protected:
        /** Protected constructor */
        explicit inline UIntBinary(const Hash::Hash &h, const CUID::CUID &cuid_,
                                   const Expr::BasePtr &e, const UInt i)
            : Base { h, cuid_ }, expr { e }, integer { i } {}
    };

    /** Default virtual destructor */
    UIntBinary::~UIntBinary() noexcept = default;

    /** Returns true if T is int binary */
    template <typename T> UTIL_ICCBOOL is_uint_binary { Util::Type::Is::ancestor<UIntBinary, T> };

} // namespace Op

#endif
