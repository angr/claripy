/**
 * @file
 * @brief This file defines a method to create an Expression with an Invert Op
 */
#ifndef __CREATE_INVERT_HPP__
#define __CREATE_INVERT_HPP__

#include "constants.hpp"
#include "private/size.hpp"


namespace Create {

    /** Create a Expression with an invert op */
    template <typename T> EBasePtr invert(EAnVec &&av, const EBasePtr &x) {

        // For brevity
        namespace Ex = Expression;
        using namespace Simplification;
        namespace Err = Error::Expression;

        // Type checks
        static_assert(Utils::qualified_is_in<T, Ex::BV, Ex::Bool>,
                      "Create::invert argument types must be of type BV or Bool");
        static_assert(Op::is_unary<Op::Invert>, "Create::neg assumes Op::Invert is unary");
        Utils::affirm<Err::Type>(Ex::is_t<T>(x), "Create::invert operand must be of type T");

        // Construct expression
        if constexpr (Utils::is_ancestor<Ex::Bits, T>) {
            return simplify(Ex::factory<T>(std::forward<EAnVec>(av), x->symbolic,
                                           Op::factory<Op::Invert>(x), Private::size(x)));
        }
        else {
            return simplify(
                Ex::factory<T>(std::forward<EAnVec>(av), x->symbolic, Op::factory<Op::Invert>(x)));
        }
    }

} // namespace Create

#endif
