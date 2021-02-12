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

        // Dynamic checks
        Utils::affirm<Err::Type>(Ex::is_t<Ex::BV>(left),
                                 "Create::sub operands must be of type Expression::BV");
        Utils::affirm<Err::Type>(Ex::are_same<true>(left, right),
                                 "Create::sub operands must be of the same size and type");

        // Construct expression
        return simplify(
            Ex::factory<Ex::BV>(std::forward<EAnVec>(av), left->symbolic || right->symbolic,
                                Op::factory<Op::Sub>(left, right), Private::size(left)));
    }

} // namespace Create

#endif
