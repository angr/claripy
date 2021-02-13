/**
 * @file
 * @brief This file defines a method to create an Expression with a Reverse Op
 */
#ifndef __CREATE_REVERSE_HPP__
#define __CREATE_REVERSE_HPP__

#include "constants.hpp"
#include "private/size.hpp"


namespace Create {

    /** Create a Expression with an reverse op */
    EBasePtr reverse(EAnVec &&av, const EBasePtr &x) {

        // For brevity
        namespace Ex = Expression;
        using namespace Simplification;
        namespace Err = Error::Expression;

        // Type checks
        static_assert(Op::is_unary<Op::Reverse>, "Create::reverse assumes Op::Reverse is unary");
        Utils::affirm<Err::Type>(Ex::is_t<Ex::BV>(x),
                                 "Create::reverse operand must be of type BV");

        // Construct expression
        return simplify(Ex::factory<Ex::BV>(std::forward<EAnVec>(av), x->symbolic,
                                            Op::factory<Op::Reverse>(x), Private::size(x)));
    }

} // namespace Create

#endif
