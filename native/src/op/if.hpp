/**
 * @file
 * @brief This file defines the Op class representing an If statement
 */
#ifndef R_SRC_OP_IF_HPP_
#define R_SRC_OP_IF_HPP_

#include "base.hpp"


namespace Op {

    /** The op class: If */
    class If final : public Base {
        OP_FINAL_INIT(If, "", 0);

      public:
        /** If condition: This must be an Expr::Bool pointer
         *  Note: We leave it as a base for optimizations purposes
         */
        const Expr::BasePtr cond;
        /** If true expr */
        const Expr::BasePtr if_true;
        /** If false expr */
        const Expr::BasePtr if_false;

        /** repr */
        inline void repr_stream(std::ostream &out) const final {
            out << R"|({ "name":")|" << op_name() << R"|(", "cond":)|";
            cond->repr_stream(out);
            out << R"|(, "if_true":)|";
            if_true->repr_stream(out);
            out << R"|(, "if_false":)|";
            if_false->repr_stream(out);
            out << " }";
        }

        /** Adds the raw expr children of the expr to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        inline void unsafe_add_reversed_children(Stack &s) const final {
            s.emplace(if_false.get());
            s.emplace(if_true.get());
            s.emplace(cond.get());
        }

        /** Appends the expr children of the expr to the given vector
         *  Note: This should only be used when returning children to python
         */
        inline std::vector<ArgVar> python_children() const final {
            return { cond, if_true, if_false };
        }

      private:
        /** Protected constructor
         *  Ensure that cond is a bool
         */
        explicit inline If(const Hash::Hash &h, const Expr::BasePtr &c, const Expr::BasePtr &if_tru,
                           const Expr::BasePtr &if_fal)
            : Base { h, static_cuid }, cond { c }, if_true { if_tru }, if_false { if_fal } {
            using Err = Error::Expr::Type;
            UTIL_ASSERT(Err, CUID::is_t<Expr::Bool>(cond), "Condition expr must be a boolean");
            const bool same { Expr::are_same_type<true>(if_true, if_false) };
            UTIL_ASSERT(Err, same, "if_true must be of the same type and size as if_false");
        }
    };

} // namespace Op

#endif
