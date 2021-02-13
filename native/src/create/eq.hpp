/**
 * @file
 * @brief This file defines a method to create an Expression with an Eq Op
 */
#ifndef __CREATE_EQ_HPP__
#define __CREATE_EQ_HPP__

#include "constants.hpp"
#include "private/size.hpp"


namespace Create {

    /** Create a Bool Expression with an Eq op */
    template <typename T> EBasePtr eq(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {

        // For brevity
        namespace Ex = Expression;
        using namespace Simplification;

        // Static checks
        static_assert(Utils::qualified_is_in<T, Ex::FP, Ex::Bool, Ex::BV, Ex::String>,
                      "Create::eq argument types must be of type FP, Bool, BV, or String");
        static_assert(Op::is_binary<Op::Eq>, "Create::eq assumes Op::Eq is binary");

        // Construct expression
        return simplify(Ex::factory<Ex::Bool>(std::forward<EAnVec>(av),
                                              left->symbolic || right->symbolic,
                                              Op::factory<Op::Eq>(left, right)));
    }

} // namespace Create

#endif
