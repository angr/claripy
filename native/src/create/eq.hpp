/**
 * @file
 * @brief This file defines a function to construct a Bool Expression with an Eq Op
 * Create contains a set of functions that wrap expression and op constructors
 */
#ifndef __CREATE_EQ_HPP__
#define __CREATE_EQ_HPP__

#include "../expression.hpp"
#include "../op.hpp"
#include "../simplification.hpp"


namespace Create {

    /** Create a Bool Expression with an Eq op */
    template <typename Left, typename Right>
    inline Factory::Ptr<Expression::Bool> eq(const Factory::Ptr<Left> &left,
                                             const Factory::Ptr<Right> &right,
                                             Expression::Base::AnnotationVec &&av) {
        // Static checks
        static_assert(Utils::is_ancestor<Expression::Base, Left>,
                      "Create::eq Left must derive from Expression::Base");
        static_assert(Utils::is_ancestor<Expression::Base, Right>,
                      "Create::eq Right must derive from Expression::Base");
        // Simplify arguments
        auto simp_left { Simplification::simplify(Utils::up_cast<Expression::Base>(left)) };
        auto simp_right { Simplification::simplify(Utils::up_cast<Expression::Base>(right)) };
        // Construct expression
        auto unsimp_ret { Expression::factory<Expression::Bool>(
            simp_left->symbolic || simp_right->symbolic,
            Op::factory<Op::Eq>(simp_left, simp_right),
            std::forward<Expression::Base::AnnotationVec>(av)) };
        // Simplify expression
        return Utils::static_down_cast<Expression::Bool>(Simplification::simplify(unsimp_ret));
    }

} // namespace Create

#endif
