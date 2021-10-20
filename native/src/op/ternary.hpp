/**
 * @file
 * @brief A ternary Op; takes three inputs of the same type
 */
#ifndef R_OP_TERNARY_HPP_
#define R_OP_TERNARY_HPP_

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
    class CLASS final : public ::Op::Ternary<(CONSIDERSIZE)> {                                    \
        OP_FINAL_INIT(CLASS, (X), "" __VA_ARGS__);                                                \
                                                                                                  \
      private:                                                                                    \
        /** Private constructor */                                                                \
        explicit inline CLASS(const ::Hash::Hash &h, const ::Expr::BasePtr &a,                    \
                              const ::Expr::BasePtr &b, const ::Expr::BasePtr &c)                 \
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
        const Expr::BasePtr first;
        /** Second operand */
        const Expr::BasePtr second;
        /** Third operand */
        const Expr::BasePtr third;

        /** Python's repr function (outputs json) */
        inline void repr(std::ostream &out, const bool verbose = false) const override final {
            out << R"|({ "name":")|" << op_name() << R"|(", "consider_size":)|" << std::boolalpha
                << ConsiderSize << R"|(, "first":)|";
            Expr::repr(first, out, verbose);
            out << R"|(, "second":)|";
            Expr::repr(second, out, verbose);
            out << R"|(, "third":)|";
            Expr::repr(third, out, verbose);
            out << " }";
        }

        /** Adds the raw expr children of the expr to the given stack in reverse
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
                                const Expr::BasePtr &one, const Expr::BasePtr &two,
                                const Expr::BasePtr &three)
            : Base { h, cuid_ }, first { one }, second { two }, third { three } {
            using E = Error::Expr::Type;

            // Type / size checking
            if constexpr (ConsiderSize) {
                Util::affirm<E>(Expr::are_same_type<true>(first, second),
                                WHOAMI_WITH_SOURCE "first and second types or sizes differ");
                Util::affirm<E>(Expr::are_same_type<true>(first, third),
                                WHOAMI_WITH_SOURCE "first and third types or sizes differ");
            }
            else {
                Util::affirm<E>(Expr::are_same_type<false>(first, second),
                                WHOAMI_WITH_SOURCE "first and second types differ");
                Util::affirm<E>(Expr::are_same_type<false>(first, third),
                                WHOAMI_WITH_SOURCE "first and third types differ");
            }
        }
    };

    /** Default virtual destructor */
    template <bool B> Ternary<B>::~Ternary() noexcept = default;

    /** Returns true if T is ternary */
    template <typename T>
    UTILS_ICCBOOL is_ternary { Util::is_ancestor<Ternary<true>, T> ||
                               Util::is_ancestor<Ternary<false>, T> };

} // namespace Op

#endif
