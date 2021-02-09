/**
 * @file
 * @brief This file defines a method to create an Expression with an Eq Op
 */
#ifndef __CREATE_EQ_HPP__
#define __CREATE_EQ_HPP__

#include "constants.hpp"


namespace Create {

    /** Create a Bool Expression with an Eq op */
    template <typename T> BasePtr eq(const BasePtr &left, const BasePtr &right, AnVec &&av) {

        // For brevity
        namespace Ex = Expression;
        using namespace Simplification;

        // Static checks
        static_assert(Utils::qualified_is_in<T, Ex::FP, Ex::Bool, Ex::BV, Ex::String>,
                      "Create::eq argument types must be of type FP, Bool, BV, or String");

        // Dynamic checks
        if constexpr (Utils::is_exactly_same<T, Ex::BV>) {
            Utils::affirm<Error::Expression::Operation>(
                dynamic_cast<CTSC<CSized>>(left.get())->size ==
                    dynamic_cast<CTSC<CSized>>(right.get())->size,
                "Operand sizes must be the same to invoke Create::eq");
        }

        // Construct expression
        return simplify(Ex::factory<Ex::Bool>(left->symbolic || right->symbolic,
                                              Op::factory<Op::Eq>(left, right),
                                              std::forward<AnVec>(av)));
    }

} // namespace Create

#endif
