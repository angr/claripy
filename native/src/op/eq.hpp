/**
 * @file
 * @brief The OP representing the == comparison
 */
#ifndef __OP_EQ_HPP__
#define __OP_EQ_HPP__

#include "base.hpp"

#include <memory>


// Forward declarations
namespace Expression {
    class Base;
    class Bool;
} // namespace Expression

namespace Op {

    /** The comparison op class: Eq */
    class Eq final : public Base {
        OP_FINAL_INIT(Eq)
      public:
        /** Left operand */
        const Factory::Ptr<Expression::Base> left;
        /** Right operand */
        const Factory::Ptr<Expression::Base> right;

      private:
        /** Protected constructor */
        explicit inline Eq(const Hash::Hash &h, const Factory::Ptr<Expression::Base> &l,
                           const Factory::Ptr<Expression::Base> &r)
            : Base { h, static_cuid }, left { l }, right { r } {}
    };

} // namespace Op

#endif
