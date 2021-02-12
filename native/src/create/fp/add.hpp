/**
 * @file
 * @brief This file defines a method to create an Expression with an FP::Add Op
 */
#ifndef __CREATE_FP_ADD_HPP__
#define __CREATE_FP_ADD_HPP__

#include "constants.hpp"

#include "../../mode.hpp"


namespace Create::FP {

    /** Create a Expression with an Add op */
    inline EBasePtr add(EAnVec &&av, const Expression::BasePtr &left,
                        const Expression::BasePtr &right, const Mode::FP mode) {

        // For brevity
        namespace Ex = Expression;
        using namespace Simplification;
        namespace Err = Error::Expression;

        // Static checks
        static_assert(std::is_final_v<Ex::FP>,
                      "Create::FP::add's assumes Expression::FP is final");

        // Dynamic type checks
        Utils::affirm<Err::Type>(Ex::is_t<Ex::FP>(left),
                                 "Create::FP::add left operands must be of type Expression::FP");
        Utils::affirm<Err::Type>(Ex::is_t<Ex::FP>(right),
                                 "Create::FP::add right operands must be of type Expression::FP");

        // Size check (static casts are safe because of previous checks)
        const auto size { static_cast<CTSC<Ex::BV>>(left.get())->size };
        Utils::affirm<Err::Size>(static_cast<CTSC<Ex::BV>>(right.get())->size == size,
                                 "Create::FP::add requires both operands be of the same size");

        // Create expression
        return simplify(Ex::factory<Expression::FP>(
            std::forward<EAnVec>(av), left->symbolic || right->symbolic,
            Op::factory<Op::FP::Add>(left, right, mode), size));
    }

} // namespace Create::FP

#endif
