/**
 * @file
 * @brief This file defines a method to create an Expression with an FP::Add Op
 */
#ifndef __CREATE_FP_ADD_HPP__
#define __CREATE_FP_ADD_HPP__

#include "constants.hpp"

#include "../../mode.hpp"
#include "../private/size.hpp"


namespace Create::FP {

    /** Create a Expression with an Add op */
    inline EBasePtr add(EAnVec &&av, const Expression::BasePtr &left,
                        const Expression::BasePtr &right, const Mode::FP mode) {

        // For brevity
        namespace Ex = Expression;
        using namespace Simplification;
        namespace Err = Error::Expression;

        // Type check
        static_assert(Op::FP::is_modebinary<Op::FP::Add>,
                      "Create::FP::add assumes Op::FP::Add is Op::FP::ModeBinary");
        Utils::affirm<Err::Type>(Ex::is_t<Ex::FP>(left),
                                 "Create::FP::add left operands must be of type Expression::FP");

        // Create expression
        return simplify(Ex::factory<Expression::FP>(
            std::forward<EAnVec>(av), left->symbolic || right->symbolic,
            Op::factory<Op::FP::Add>(left, right, mode), Private::size(left)));
    }

} // namespace Create::FP

#endif
