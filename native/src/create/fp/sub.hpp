/**
 * @file
 * @brief This file defines a method to create an Expression with an FP::sub Op
 */
#ifndef __CREATE_FP_SUB_HPP__
#define __CREATE_FP_SUB_HPP__

#include "constants.hpp"

#include "../../mode.hpp"
#include "../private/size.hpp"


namespace Create::FP {

    /** Create a Expression with an sub op */
    inline EBasePtr sub(EAnVec &&av, const Expression::BasePtr &left,
                        const Expression::BasePtr &right, const Mode::FP mode) {

        // For brevity
        namespace Ex = Expression;
        using namespace Simplification;
        namespace Err = Error::Expression;

        // Type check
        static_assert(Op::FP::is_modebinary<Op::FP::Sub>,
                      "Create::FP::sub assumes Op::FP::Sub is Op::FP::ModeBinary");
        Utils::affirm<Err::Type>(Ex::is_t<Ex::FP>(left),
                                 "Create::FP::sub left operands must be of type Expression::FP");

        // Create expression
        return simplify(Ex::factory<Expression::FP>(
            std::forward<EAnVec>(av), left->symbolic || right->symbolic,
            Op::factory<Op::FP::Sub>(left, right, mode), Private::size(left)));
    }

} // namespace Create::FP

#endif
