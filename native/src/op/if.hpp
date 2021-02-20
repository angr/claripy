/**
 * @file
 * @brief This file defines the Op class representing an If statement
 */
#ifndef __OP_IF_HPP__
#define __OP_IF_HPP__

#include "base.hpp"


namespace Op {

    /** The op class: If */
    class If final : public Base {
        OP_FINAL_INIT(If)
      public:
        /** If condition: This must be an Expression::Bool pointer
         *  Note: We leave it as a base for optimizations purposes
         */
        const Expression::BasePtr cond;
        /** If true expression */
        const Expression::BasePtr if_true;
        /** If false expression */
        const Expression::BasePtr if_false;

      private:
        /** Protected constructor
         *  Ensure that cond is a bool
         */
        explicit inline If(const Hash::Hash &h, const Expression::BasePtr &c,
                           const Expression::BasePtr &if_tru, const Expression::BasePtr &if_fal)
            : Base { h, static_cuid }, cond { c }, if_true { if_tru }, if_false { if_fal } {
            // For brevity
            namespace Err = Error::Expression;
            // Error checking
            Utils::affirm<Err::Type>(Expression::is_t<Expression::Bool>(cond),
                                     WHOAMI_WITH_SOURCE "Condition expression must be a boolean");
            Utils::affirm<Err::Type>(Expression::are_same<true>(if_true, if_false),
                                     WHOAMI_WITH_SOURCE
                                     "if_true must be of the same type and size as if_false");
        }
    };

} // namespace Op

#endif
