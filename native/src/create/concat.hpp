/**
 * @file
 * @brief This file defines a method to create an Expression with an Concat Op
 */
#ifndef __CREATE_CONCAT_HPP__
#define __CREATE_CONCAT_HPP__

#include "constants.hpp"


namespace Create {

    /** Create a Bool Expression with an Eq op */
    template <typename T> EBasePtr concat(const Ptr<T> &left, const Ptr<T> &right, EAnVec &&av) {
#if 1
        (void) left;
        (void) right;
        (void) av;
#else
        // For brevity
        namespace Ex = Expression;
        using namespace Simplification;

        // Static checks
        static_assert(Utils::qualified_is_in<T, Ex::FP, Ex::Bool, Ex::BV, Ex::String>,
                      "Create::eq argument types must be of type FP, Bool, BV, or String");

        // Dynamic checks
        if constexpr (Utils::is_exactly_same<Left, Ex::BV>) {
            Utils::affirm<Error::Expression::Operation>(
                left->size == right->size,
                "Operand sizes must be the same to invoke Create::concat");
        }

        // Construct expression
        return simplify(Ex::factory<T>(left->symbolic || right->symbolic,
                                       Op::factory<Op::Concat>(left, right),
                                       std::forward<EAnVec>(av)));
#endif
    }

} // namespace Create

#endif
