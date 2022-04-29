/**
 * @file
 * @brief A unary Op
 */
#ifndef R_SRC_OP_UNARY_HPP_
#define R_SRC_OP_UNARY_HPP_

#include "base.hpp"

#include "../error.hpp"


/** A macro used to define a trivial subclass of Unary
 *  PREFIX and TARG are passed to OP_FINAL_INIT
 */
#define OP_UNARY_TRIVIAL_SUBCLASS(CLASS, PREFIX, TARG)                                             \
    class CLASS final : public ::Op::Unary {                                                       \
        OP_FINAL_INIT(CLASS, PREFIX, TARG);                                                        \
                                                                                                   \
      private:                                                                                     \
        /** Private constructor */                                                                 \
        explicit inline CLASS(const ::Hash::Hash &h, const ::Expr::BasePtr &x)                     \
            : Unary { h, static_cuid, x } {}                                                       \
    };


namespace Op {

    /** A Unary Op class */
    class Unary : public Base {
        OP_PURE_INIT(Unary);

      public:
        /** The operand */
        const Expr::BasePtr child;

        /** repr */
        inline void repr_stream(std::ostream &out) const final {
            out << R"|({ "name":")|" << op_name() << R"|(", "child":)|";
            child->repr_stream(out);
            out << " }";
        }

        /** Appends the expr children of the expr to the given vector
         *  Note: This should only be used when returning children to python
         */
        inline std::vector<ArgVar> python_children() const final { return { child }; }

      protected:
        /** Protected constructor */
        explicit inline Unary(const Hash::Hash &h, const CUID::CUID &cuid_, const Expr::BasePtr &x)
            : Base { h, cuid_ }, child { x } {}

      private:
        /** Adds the raw expr children of the expr to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        inline void unsafe_add_reversed_children(Stack &s) const final { s.emplace(child.get()); }
    };

    /** Default virtual destructor */
    Unary::~Unary() noexcept = default;

    /** Returns true if T is unary */
    template <typename T> UTIL_ICCBOOL is_unary { Util::Type::Is::ancestor<Unary, T> };

} // namespace Op

#endif
