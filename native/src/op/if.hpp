/**
 * @file
 * @brief The OP representing an If
 */
#ifndef __OP_IF_HPP__
#define __OP_IF_HPP__

#include "base.hpp"

#include <memory>


// Forward declarations
namespace Expression {
    class Base;
    class Bool;
} // namespace Expression

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
            // Error checking
            namespace Err = Error::Expression;
            Utils::affirm<Err::Type>(cond->cuid == Expression::Bool::static_cuid,
                                     "Op::If: Condition expression must be a boolean");
            Utils::affirm<Err::Type>(if_true->cuid == if_false->cuid,
                                     "Op::If: if_true must be of the same type as if_false");
        }
    };

} // namespace Op

#endif
