/**
 * @file
 * @brief A ternary Op; takes three inputs of the same type
 */
#ifndef __OP_TERNARY_HPP__
#define __OP_TERNARY_HPP__

#include "base.hpp"


/** A macro used to define a trivial subclass of Ternary
 *  Pass template arguments to Ternary via variadic macro arguments
 *  If ConsiderSize, sizes will be compared as well when type checking if applicable
 *  Note: You can prepend templates to this if desired meant only to create distinct classes
 *  For example: template <bool Signed> OP_TERNARY_TRIVIAL_SUBCLASS(LT, true)
 */
#define OP_TERNARY_TRIVIAL_SUBCLASS(CLASS, CONSIDERSIZE)                                          \
    class CLASS final : public ::Op::Ternary<CONSIDERSIZE> {                                      \
        OP_FINAL_INIT(CLASS)                                                                      \
      private:                                                                                    \
        /** Private constructor */                                                                \
        explicit inline CLASS(const ::Hash::Hash &h, const ::Expression::BasePtr &a,              \
                              const ::Expression::BasePtr &b, const ::Expression::BasePtr &c)     \
            : Ternary { h, static_cuid, a, b, c } {}                                              \
    };


namespace Op {

    /** A Ternary Op class
     *  Operands must all be of the same type
     *  If ConsiderSize, sizes will be compared as well when type checking if applicable
     */
    template <bool ConsiderSize> class Ternary : public Base {
        OP_PURE_INIT(Ternary)
      public:
        /** First operand */
        const Expression::BasePtr first;
        /** Second operand */
        const Expression::BasePtr second;
        /** Third operand */
        const Expression::BasePtr third;

      protected:
        /** Protected constructor */
        explicit inline Ternary(const Hash::Hash &h, const CUID::CUID &cuid_,
                                const Expression::BasePtr &one, const Expression::BasePtr &two,
                                const Expression::BasePtr &three)
            : Base { h, cuid_ }, first { one }, second { two }, third { three } {
            using Err = Error::Expression::Type;

            // Type / size checking
            if constexpr (ConsiderSize) {
                Utils::affirm<Err>(Expression::are_same_type<true>(first, second),
                                   WHOAMI_WITH_SOURCE "first and second types or sizes differ");
                Utils::affirm<Err>(Expression::are_same_type<true>(first, third),
                                   WHOAMI_WITH_SOURCE "first and third types or sizes differ");
            }
            else {
                Utils::affirm<Err>(Expression::are_same_type<false>(first, second),
                                   WHOAMI_WITH_SOURCE "first and second types differ");
                Utils::affirm<Err>(Expression::are_same_type<false>(first, third),
                                   WHOAMI_WITH_SOURCE "first and third types differ");
            }
        }
    };

    /** Default virtual destructor */
    template <bool B> Ternary<B>::~Ternary() noexcept = default;

    /** Returns true if T is ternary */
    template <typename T>
    UTILS_ICCBOOL is_ternary { Utils::is_ancestor<Ternary<true>, T> ||
                               Utils::is_ancestor<Ternary<false>, T> };

} // namespace Op

#endif
