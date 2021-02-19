/**
 * @file
 * @brief An op that takes in one Expression and one intger
 */
#ifndef __OP_INTBINARY_HPP__
#define __OP_INTBINARY_HPP__

#include "base.hpp"

#include "../error.hpp"


/** A macro used to define a trivial subclass of Binary
 *  Pass template arguments to Binary via variadic macro arguments
 *  Note: You can prepend templates to this if desired meant only to create distinct classes
 *  For example: template <bool Signed> OP_INTBINARY_TRIVIAL_SUBCLASS(Foo)
 */
#define OP_INTBINARY_TRIVIAL_SUBCLASS(CLASS)                                                      \
    class CLASS final : public ::Op::IntBinary {                                                  \
        OP_FINAL_INIT(CLASS)                                                                      \
      private:                                                                                    \
        /** Private constructor */                                                                \
        explicit inline CLASS(const ::Hash::Hash &h, const ::Expression::BasePtr &e,              \
                              const Constants::Int i)                                             \
            : IntBinary { h, static_cuid, e, i } {}                                               \
    };


namespace Op {

    /** An Op class that has an Expression operand and an int operand */
    class IntBinary : public Base {
        OP_PURE_INIT(IntBinary)
      public:
        /** Expression operand */
        const Expression::BasePtr expr;
        /* Integer operand */
        const Constants::Int integer;

      protected:
        /** Protected constructor */
        explicit inline IntBinary(const Hash::Hash &h, const CUID::CUID &cuid_,
                                  const Expression::BasePtr &e, const Constants::Int i)
            : Base { h, cuid_ }, expr { e }, integer { i } {}
    };

    /** Default virtual destructor */
    IntBinary::~IntBinary() noexcept = default;

    /** Returns true if T is binary */
    template <typename T> UTILS_ICCBOOL is_int_binary { Utils::is_ancestor<IntBinary, T> };

} // namespace Op

#endif
