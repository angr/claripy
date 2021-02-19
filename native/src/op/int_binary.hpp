/**
 * @file
 * @brief An op that takes in one Expression and one intger
 */
#ifndef __OP_INTBINARY_HPP__
#define __OP_INTBINARY_HPP__

#include "base.hpp"

#include "../error.hpp"

#include <type_traits>


/** A macro used to define a trivial subclass of Binary
 *  Pass template arguments to Binary via variadic macro arguments
 *  Note: You can prepend templates to this if desired meant only to create distinct classes
 *  UNSIGNEDINT can be true or false
 *  For example: template <bool Signed> OP_INTBINARY_TRIVIAL_SUBCLASS(Foo)
 */
#define OP_INTBINARY_TRIVIAL_SUBCLASS(CLASS, UNSIGNEDINT)                                         \
    class CLASS final : public ::Op::IntBinary<UNSIGNEDINT> {                                     \
        OP_FINAL_INIT(CLASS)                                                                      \
      private:                                                                                    \
        /** Private constructor */                                                                \
        explicit inline CLASS(const ::Hash::Hash &h, const ::Expression::BasePtr &e,              \
                              const IntT i)                                                       \
            : IntBinary { h, static_cuid, e, i } {}                                               \
    };


namespace Op {

    /** An Op class that has an Expression operand and an int operand */
    template <bool UnsignedInt> class IntBinary : public Base {
        OP_PURE_INIT(IntBinary)
      public:
        /** The int type */
        using IntT = std::conditional_t<UnsignedInt, Constants::UInt, Constants::Int>;

        /** Expression operand */
        const Expression::BasePtr expr;
        /* Integer operand */
        const IntT integer;

      protected:
        /** Protected constructor */
        explicit inline IntBinary(const Hash::Hash &h, const CUID::CUID &cuid_,
                                  const Expression::BasePtr &e, const IntT i)
            : Base { h, cuid_ }, expr { e }, integer { i } {}
    };

    /** Default virtual destructor */
    template <bool B> IntBinary<B>::~IntBinary() noexcept = default;

    /** Returns true if T is int binary */
    template <typename T>
    UTILS_ICCBOOL is_int_binary { Utils::is_ancestor<IntBinary<true>, T> ||
                                  Utils::is_ancestor<IntBinary<false>, T> };

} // namespace Op

#endif
