/**
 * @file
 * @brief A binary Op; takes two inputs of the same type
 * For example: Concat(Str1, Str2)
 */
#ifndef R_SRC_OP_BINARY_HPP_
#define R_SRC_OP_BINARY_HPP_

#include "base.hpp"

#include "../error.hpp"


/** A macro used to define a trivial subclass of Binary
 *  If ConsiderSize, sizes will be compared as well when type checking if applicable
 *  PREFIX and TARG are passed to OP_FINAL_INIT
 */
#define OP_BINARY_TRIVIAL_SUBCLASS(CLASS, CONSIDERSIZE, PREFIX, TARG)                              \
    class CLASS final : public ::Op::Binary<(CONSIDERSIZE)> {                                      \
        OP_FINAL_INIT(CLASS, PREFIX, TARG);                                                        \
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
        inline std::vector<ArgVar> python_children() const final { return { left, right }; }

        /** repr */
        inline void repr_stream(std::ostream &out) const override {
            out << R"|({ "name":")|" << op_name() << R"|(", "consider_size":)|" << std::boolalpha
                << ConsiderSize << R"|(, "left":)|";
            left->repr_stream(out);
            out << R"|(, "right":)|";
            right->repr_stream(out);
            out << " }";
        }

      protected:
        /** Protected constructor */
        explicit inline Binary(const Hash::Hash &h, const CUID::CUID &cuid_, const Expr::BasePtr &l,
                               const Expr::BasePtr &r)
            : Base { h, cuid_ }, left { l }, right { r } {

            // Type / size checking
            const bool same { Expr::are_same_type<ConsiderSize>(left, right) };
            UTIL_ASSERT(Error::Expr::Type, same, "left and right differ by type",
                        ConsiderSize ? " or size" : "");
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
