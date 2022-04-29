/**
 * @file
 * @brief A ternary Op; takes three inputs of the same type
 */
#ifndef R_SRC_OP_TERNARY_HPP_
#define R_SRC_OP_TERNARY_HPP_

#include "base.hpp"


/** A macro used to define a trivial subclass of Ternary
 *  If ConsiderSize, sizes will be compared as well when type checking if applicable
 *  PREFIX is passed to OP_FINAL_INIT
 */
#define OP_TERNARY_TRIVIAL_SUBCLASS(CLASS, CONSIDERSIZE, PREFIX)                                   \
    class CLASS final : public ::Op::Ternary<(CONSIDERSIZE)> {                                     \
        OP_FINAL_INIT(CLASS, PREFIX);                                                              \
                                                                                                   \
      private:                                                                                     \
        /** Private constructor */                                                                 \
        explicit inline CLASS(const ::Hash::Hash &h, const ::Expr::BasePtr &a,                     \
                              const ::Expr::BasePtr &b, const ::Expr::BasePtr &c)                  \
            : Ternary { h, static_cuid, a, b, c } {}                                               \
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

        /** repr */
        inline void repr_stream(std::ostream &out) const final {
            out << R"|({ "name":")|" << op_name() << R"|(", "consider_size":)|" << std::boolalpha
                << ConsiderSize << R"|(, "first":)|";
            first->repr_stream(out);
            out << R"|(, "second":)|";
            second->repr_stream(out);
            out << R"|(, "third":)|";
            third->repr_stream(out);
            out << " }";
        }

        /** Appends the expr children of the expr to the given vector
         *  Note: This should only be used when returning children to python
         */
        inline std::vector<ArgVar> python_children() const final {
            return { first, second, third };
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
                UTIL_ASSERT(E, Expr::are_same_type<true>(first, second),
                            "first and second types or sizes differ");
                UTIL_ASSERT(E, Expr::are_same_type<true>(first, third),
                            "first and third types or sizes differ");
            }
            else {
                UTIL_ASSERT(E, Expr::are_same_type<false>(first, second),
                            "first and second types differ");
                UTIL_ASSERT(E, Expr::are_same_type<false>(first, third),
                            "first and third types differ");
            }
        }

      private:
        /** Adds the raw expr children of the expr to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        inline void unsafe_add_reversed_children(Stack &s) const final {
            s.emplace(third.get());
            s.emplace(second.get());
            s.emplace(first.get());
        }
    };

    /** Default virtual destructor */
    template <bool B> Ternary<B>::~Ternary() noexcept = default;

    /** Returns true if T is ternary */
    template <typename T>
    UTIL_ICCBOOL is_ternary { Util::Type::Is::ancestor<Ternary<true>, T> ||
                              Util::Type::Is::ancestor<Ternary<false>, T> };

} // namespace Op

#endif
