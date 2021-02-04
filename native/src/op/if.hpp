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
        /** If condition */
        const Factory::Ptr<Expression::Bool> cond;
        /** If true expression */
        const Factory::Ptr<Expression::Base> if_true;
        /** If false expression */
        const Factory::Ptr<Expression::Base> if_false;

      private:
        /** Protected constructor */
        explicit inline If(const Hash::Hash &h, const Factory::Ptr<Expression::Bool> &c,
                           const Factory::Ptr<Expression::Base> &if_tru,
                           const Factory::Ptr<Expression::Base> &if_fal)
            : Base { h, static_cuid }, cond { c }, if_true { if_tru }, if_false { if_fal } {}
    };

} // namespace Op

#endif
