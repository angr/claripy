/**
 * @file
 * @brief This file defines the Op class representing an If statement
 */
#ifndef R_OP_IF_HPP_
#define R_OP_IF_HPP_

#include "base.hpp"


namespace Op {

    /** The op class: If */
    class If final : public Base {
        OP_FINAL_INIT(If, 0);

      public:
        /** If condition: This must be an Expr::Bool pointer
         *  Note: We leave it as a base for optimizations purposes
         */
        const Expr::BasePtr cond;
        /** If true expr */
        const Expr::BasePtr if_true;
        /** If false expr */
        const Expr::BasePtr if_false;

        /** Python's repr function (outputs json) */
        inline void repr(std::ostream &out, const bool verbose = false) const override final {
            out << R"|({ "name":")|" << op_name() << R"|(", "cond":)|";
            Expr::repr(cond, out, verbose);
            out << R"|(, "if_true":)|";
            Expr::repr(if_true, out, verbose);
            out << R"|(, "if_false":)|";
            Expr::repr(if_false, out, verbose);
            out << " }";
        }

        /** Adds the raw expr children of the expr to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        inline void add_reversed_children(Stack &s) const override final {
            s.emplace(if_false.get());
            s.emplace(if_true.get());
            s.emplace(cond.get());
        }

      private:
        /** Protected constructor
         *  Ensure that cond is a bool
         */
        explicit inline If(const Hash::Hash &h, const Expr::BasePtr &c,
                           const Expr::BasePtr &if_tru, const Expr::BasePtr &if_fal)
            : Base { h, static_cuid }, cond { c }, if_true { if_tru }, if_false { if_fal } {
            // For brevity
            namespace Err = Error::Expr;
            // Error checking
            Util::affirm<Err::Type>(CUID::is_t<Expr::Bool>(cond),
                                    WHOAMI "Condition expr must be a boolean");
            Util::affirm<Err::Type>(Expr::are_same_type<true>(if_true, if_false), WHOAMI
                                    "if_true must be of the same type and size as if_false");
        }
    };

} // namespace Op

#endif
