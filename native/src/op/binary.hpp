/**
 * @file
 * @brief A binary Op; takes two inputs of the same type
 * For example: Concat(Str1, Str2)
 */
#ifndef R_OP_BINARY_HPP_
#define R_OP_BINARY_HPP_

#include "base.hpp"

#include "../error.hpp"


/** A macro used to define a trivial subclass of Binary
 *  Pass template arguments to Binary via variadic macro arguments
 *  If ConsiderSize, sizes will be compared as well when type checking if applicable
 *  Note: You can prepend templates to this if desired meant only to create distinct classes
 *  For example: template <bool Signed> OP_BINARY_TRIVIAL_SUBCLASS(LT, true)
 *  An additional argument can be passed as the prefix to the desired debug name of the class
 *  For example, "FP::" may be desired for an FP op
 *  X can be any int but it must be different between different templates of the same class
 *  For example, Foo<int> must give a different X from Foo<bool>
 */
#define OP_BINARY_TRIVIAL_SUBCLASS(CLASS, CONSIDERSIZE, X, ...)                                    \
    class CLASS final : public ::Op::Binary<(CONSIDERSIZE)> {                                      \
        OP_FINAL_INIT(CLASS, (X), "" __VA_ARGS__);                                                 \
                                                                                                   \
      private:                                                                                     \
        /** Private constructor */                                                                 \
        explicit inline CLASS(const ::Hash::Hash &h, const ::Expr::BasePtr &l,                     \
                              const ::Expr::BasePtr &r)                                            \
            : Binary { h, static_cuid, l, r } {}                                                   \
    };


namespace Op {

    /** A Binary Op class
     *  Operands must all be of the same type
     *  If ConsiderSize, sizes will be compared as well when type checking if applicable
     */
    template <bool ConsiderSize> class Binary : public Base {
        OP_PURE_INIT(Binary);

      public:
        /** Left operand */
        const Expr::BasePtr left;
        /** Right operand */
        const Expr::BasePtr right;

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
            v.emplace_back(left);
            v.emplace_back(right);
        }

        /** Python's repr function (outputs json) */
        inline void repr(std::ostream &out) const override {
            repr_helper(out);
            out << " }";
        }

      protected:
        /** Protected constructor */
        explicit inline Binary(const Hash::Hash &h, const CUID::CUID &cuid_, const Expr::BasePtr &l,
                               const Expr::BasePtr &r)
            : Base { h, cuid_ }, left { l }, right { r } {
            using E = Error::Expr::Type;

            // Type / size checking
            if constexpr (ConsiderSize) {
                Util::affirm<E>(Expr::are_same_type<true>(left, right),
                                WHOAMI "left and right types or sizes differ");
            }
            else {
                Util::affirm<E>(Expr::are_same_type<false>(left, right),
                                WHOAMI "left and right types differ");
            }
        }

        /** Python's repr function (outputs json), but without the closing '}' */
        inline void repr_helper(std::ostream &out) const {
            out << R"|({ "name":")|" << op_name() << R"|(", "consider_size":)|" << std::boolalpha
                << ConsiderSize << R"|(, "left":)|";
            left->repr(out);
            out << R"|(, "right":)|";
            right->repr(out);
        }
    };

    /** Default virtual destructor */
    template <bool B> Binary<B>::~Binary() noexcept = default;

    /** Returns true if T is binary */
    template <typename T>
    UTIL_ICCBOOL is_binary { Util::Type::Is::ancestor<Binary<true>, T> ||
                             Util::Type::Is::ancestor<Binary<false>, T> };

} // namespace Op

#endif
