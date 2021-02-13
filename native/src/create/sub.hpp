/**
 * @file
 * @brief This file defines a method to create an Expression with an sub Op
 */
#ifndef __CREATE_SUB_HPP__
#define __CREATE_SUB_HPP__

#include "constants.hpp"
#include "private/size.hpp"


namespace Create {

    /** Create a Bool Expression with an sub op */
    EBasePtr sub(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {

        // For brevity
        namespace Ex = Expression;
        namespace Err = Error::Expression;
        using namespace Simplification;

        // Type checks
        static_assert(Op::is_binary<Op::Sub>, "Create::sub assumes Op::Sub is binary");
        Utils::affirm<Err::Type>(Ex::is_t<Ex::BV>(left),
                                 "Create::sub operands must be of type Expression::BV");

        // Construct expression
        return simplify(
            Ex::factory<Ex::BV>(std::forward<EAnVec>(av), left->symbolic || right->symbolic,
                                Op::factory<Op::Sub>(left, right), Private::size(left)));
    }

} // namespace Create

#endif
