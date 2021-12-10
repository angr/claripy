/**
 * @file
 * @brief A floating point binary Op; takes an FP mode and two inputs of the same type
 */
#ifndef R_OP_FP_MODEBINARY_HPP_
#define R_OP_FP_MODEBINARY_HPP_

#include "../../mode.hpp"
#include "../binary.hpp"


/** A macro used to define a trivial subclass of ModeBinary
 *  An additional argument can be passed as the prefix to the desired debug name of the class
 *  For example, "FP::" may be desired for an FP op
 *  X can be anything, but must be different between different templates of the same class
 *  For example, Foo<int> must give a different X from Foo<bool>
 */
#define OP_FP_MODEBINARY_TRIVIAL_SUBCLASS(CLASS, X, ...)                                           \
    class CLASS final : public ModeBinary {                                                        \
        OP_FINAL_INIT(CLASS, (X), "" __VA_ARGS__);                                                 \
                                                                                                   \
      private:                                                                                     \
        /** Private constructor */                                                                 \
        explicit inline CLASS(const ::Hash::Hash &h, const ::Expr::BasePtr &l,                     \
                              const ::Expr::BasePtr &r, const ::Mode::FP::Rounding m)              \
            : ModeBinary { h, static_cuid, l, r, m } {}                                            \
    };


namespace Op::FP {

    /** An FP Binary Op class
     *  Operands must all be of the same type and size
     */
    class ModeBinary : public Base {
        OP_PURE_INIT(ModeBinary);

      public:
        /** FP Mode */
        const Mode::FP::Rounding mode;
        /** Left operand */
        const Expr::BasePtr left;
        /** Right operand */
        const Expr::BasePtr right;

        /** Python's repr function (outputs json) */
        inline void repr(std::ostream &out) const final {
            out << R"|({ "name":")|" << op_name() << R"|(", "mode":)|" << Util::to_underlying(mode)
                << R"|(, "left":)|";
            left->repr(out);
            out << R"|(, "right":)|";
            right->repr(out);
            out << " }";
        }

        /** Adds the raw expr children of the expr to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        inline void unsafe_add_reversed_children(Stack &s) const final {
            s.emplace(right.get());
            s.emplace(left.get());
        }

        /** Appends the expr children of the expr to the given vector
         *  Note: This should only be used when returning children to python
         */
        inline void python_children(std::vector<ArgVar> &v) const final {
            v.emplace_back(mode);
            v.emplace_back(left);
            v.emplace_back(right);
        }

      protected:
        /** Protected constructor */
        explicit inline ModeBinary(const Hash::Hash &h, const CUID::CUID &cuid_,
                                   const Expr::BasePtr &l, const Expr::BasePtr &r,
                                   const Mode::FP::Rounding m)
            : Base { h, cuid_ }, mode { m }, left { l }, right { r } {
            const bool same { Expr::are_same_type<true>(left, right) };
            UTIL_ASSERT(Error::Expr::Type, same, "left and right types or sizes differ");
        }
    };

    /** Default virtual destructor */
    ModeBinary::~ModeBinary() noexcept = default;

    /** Returns true if T is ModeBinary */
    template <typename T> UTIL_ICCBOOL is_mode_binary { Util::Type::Is::ancestor<ModeBinary, T> };

} // namespace Op::FP

#endif
