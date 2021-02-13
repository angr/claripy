/**
 * @file
 * @brief This file defines a method to create an Expression with an Neg Op
 */
#ifndef __CREATE_NEG_HPP__
#define __CREATE_NEG_HPP__

#include "constants.hpp"
#include "private/size.hpp"


namespace Create {

    /** Create a Expression with an neg op */
    template <typename T> EBasePtr neg(EAnVec &&av, const EBasePtr &x) {

        // For brevity
        namespace Ex = Expression;
        using namespace Simplification;
        namespace Err = Error::Expression;

        // Type checks
        static_assert(Utils::qualified_is_in<T, Ex::BV, Ex::FP>,
                      "Create::neg argument types must be of type BV or FP");
        static_assert(Op::is_unary<Op::Neg>, "Create::neg assumes Op::Neg is unary");
        Utils::affirm<Err::Type>(Ex::is_t<T>(x), "Create::neg operand must be of type T");

        // Construct expression
        return simplify(Ex::factory<T>(std::forward<EAnVec>(av), x->symbolic,
                                       Op::factory<Op::Neg>(x), Private::size(x)));
    }

} // namespace Create

#endif
