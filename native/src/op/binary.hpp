/**
 * @file
 * @brief A binary Op; takes two inputs of the same type
 * For example: Concat(Str1, Str2)
 */
#ifndef __OP_BINARY_HPP__
#define __OP_BINARY_HPP__

#include "base.hpp"

#include "../error.hpp"


/** A macro used to define a trivial subclass of Binary
 *  Pass template arguments to Binary via variadic macro arguments
 *  If ConsiderSize, sizes will be compared as well when type checking if applicable
 *  Note: You can prepend templates to this if desired meant only to create distinct classes
 *  For example: template <bool Signed> OP_BINARY_TRIVIAL_SUBCLASS(LT, true)
 */
#define OP_BINARY_TRIVIAL_SUBCLASS(CLASS, CONSIDERSIZE)                                           \
    class CLASS final : public ::Op::Binary<CONSIDERSIZE> {                                       \
        OP_FINAL_INIT(CLASS)                                                                      \
      private:                                                                                    \
        /** Private constructor */                                                                \
        explicit inline CLASS(const ::Hash::Hash &h, const ::Expression::BasePtr &l,              \
                              const ::Expression::BasePtr &r)                                     \
            : Binary { h, static_cuid, l, r } {}                                                  \
    };


namespace Op {

    /** A Binary Op class
     *  Operands must all be of the same type
     *  If ConsiderSize, sizes will be compared as well when type checking if applicable
     */
    template <bool ConsiderSize> class Binary : public Base {
        OP_PURE_INIT(Binary)
      public:
        /** Left operand */
        const Expression::BasePtr left;
        /** Right operand */
        const Expression::BasePtr right;

      protected:
        /** Protected constructor */
        explicit inline Binary(const Hash::Hash &h, const CUID::CUID &cuid_,
                               const Expression::BasePtr &l, const Expression::BasePtr &r)
            : Base { h, cuid_ }, left { l }, right { r } {
            using Err = Error::Expression::Type;

            // Type / size checking
            if constexpr (ConsiderSize) {
                Utils::affirm<Err>(Expression::are_same_type<true>(left, right),
                                   WHOAMI_WITH_SOURCE "left and right types or sizes differ");
            }
            else {
                Utils::affirm<Err>(Expression::are_same_type<false>(left, right),
                                   WHOAMI_WITH_SOURCE "left and right types differ");
            }
        }
    };

    /** Default virtual destructor */
    template <bool B> Binary<B>::~Binary() noexcept = default;

    /** Returns true if T is binary */
    template <typename T>
    UTILS_ICCBOOL is_binary { Utils::is_ancestor<Binary<true>, T> ||
                              Utils::is_ancestor<Binary<false>, T> };

} // namespace Op

#endif
