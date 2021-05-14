/**
 * @file
 * @brief An op that takes in one Expression and one intger
 */
#ifndef R_OP_UINTBINARY_HPP_
#define R_OP_UINTBINARY_HPP_

#include "base.hpp"

#include "../error.hpp"

#include <type_traits>


/** A macro used to define a trivial subclass of Binary
 *  Pass template arguments to Binary via variadic macro arguments
 *  Note: You can prepend templates to this if desired meant only to create distinct classes
 *  UNSIGNEDINT can be true or false
 *  For example: template <bool Signed> OP_INTBINARY_TRIVIAL_SUBCLASS(Foo)
 *  An additional argument can be passed as the prefix to the desired debug name of the class
 *  For example, "FP::" may be desired for an FP op
 *  X can be anything, but must be different between different templates of the same class
 *  For example, Foo<int> must give a different X from Foo<bool>
 */
#define OP_UINTBINARY_TRIVIAL_SUBCLASS(CLASS, X, ...)                                             \
    class CLASS final : public ::Op::UIntBinary {                                                 \
        OP_FINAL_INIT(CLASS, (X), "" __VA_ARGS__);                                                \
                                                                                                  \
      private:                                                                                    \
        /** Private constructor */                                                                \
        explicit inline CLASS(const ::Hash::Hash &h, const ::Expression::BasePtr &e,              \
                              const Constants::UInt i)                                            \
            : UIntBinary { h, static_cuid, e, i } {}                                              \
    };


namespace Op {

    /** An Op class that has an Expression operand and an int operand */
    class UIntBinary : public Base {
        OP_PURE_INIT(UIntBinary);

      public:
        /** Expression operand */
        const Expression::BasePtr expr;
        /* Integer operand */
        const Constants::UInt integer;

        /** Python's repr function (outputs json) */
        inline void repr(std::ostringstream &out,
                         const bool verbose = false) const override final {
            out << R"|({ "name":")|" << op_name() << R"|(", "expr":)|";
            Expression::repr(expr, out, verbose);
            out << R"|(, "integer":)|" << integer << " }";
        }

        /** Add's the raw expression children of the expression to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        inline void add_reversed_children(Stack &s) const override final { s.emplace(expr.get()); }

      protected:
        /** Protected constructor */
        explicit inline UIntBinary(const Hash::Hash &h, const CUID::CUID &cuid_,
                                   const Expression::BasePtr &e, const Constants::UInt i)
            : Base { h, cuid_ }, expr { e }, integer { i } {}
    };

    /** Default virtual destructor */
    UIntBinary::~UIntBinary() noexcept = default;

    /** Returns true if T is int binary */
    template <typename T> UTILS_ICCBOOL is_uint_binary { Utils::is_ancestor<UIntBinary, T> };

} // namespace Op

#endif
