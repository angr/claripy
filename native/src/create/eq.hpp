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
        // For brevity
        namespace Ex = Expression;
        using AnVec = Ex::Base::AnnotationVec;
        const constexpr auto &simplify { Simplification::simplify };
        // Static checks
        static_assert(Utils::is_exactly_same<Left, Right>,
                      "Create::eq Left and Right must be of the same type");
        static_assert(Utils::qualified_is_in<Left, Ex::FP, Ex::Bool, Ex::BV, Ex::String>,
                      "Create::eq argument types must be of type FP, Bool, BV, or String");
        // Construct expression
        auto unsimp_ret { Ex::factory<Ex::Bool>(left->symbolic || right->symbolic,
                                                Op::factory<Op::Eq>(left, right),
                                                std::forward<AnVec>(av)) };
        // Simplify expression
        return Utils::static_down_cast<Ex::Bool>(simplify(unsimp_ret));
    }

} // namespace Create

#endif
