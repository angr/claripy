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
 *  An additional argument can be passed as the prefix to the desired debug name of the class
 *  For example, "FP::" may be desired for an FP op
 *  X can be anything, but must be different between different templates of the same class
 *  For example, Foo<int> must give a different X from Foo<bool>
 */
#define OP_TERNARY_TRIVIAL_SUBCLASS(CLASS, CONSIDERSIZE, X, ...)                                  \
    class CLASS final : public ::Op::Ternary<CONSIDERSIZE> {                                      \
        OP_FINAL_INIT(CLASS, (X), "" __VA_ARGS__);                                                \
                                                                                                  \
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
        OP_PURE_INIT(Ternary);

      public:
        /** First operand */
        const Expression::BasePtr first;
        /** Second operand */
        const Expression::BasePtr second;
        /** Third operand */
        const Expression::BasePtr third;

        /** Python's repr function (outputs json) */
        inline void repr(std::ostringstream &out,
                         const bool verbose = false) const override final {
            out << R"|({ "name":")|" << op_name() << R"|(", "consider_size":)|" << ConsiderSize
                << R"|(, "first":)|";
            Expression::repr(first, out, verbose);
            out << R"|(, "second":)|";
            Expression::repr(second, out, verbose);
            out << R"|(, "thrid":)|";
            Expression::repr(third, out, verbose);
            out << " }";
        }

        /** Add's the raw expression children of the expression to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        inline void add_reversed_children(Stack &s) const override final {
            s.emplace(third.get());
            s.emplace(second.get());
            s.emplace(first.get());
        }

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
