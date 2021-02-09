/**
 * @file
 * @brief This file defines a method to create an Expression with an Add Op
 */
#ifndef __CREATE_ADD_HPP__
#define __CREATE_ADD_HPP__

#include "constants.hpp"


namespace Create {

    /** Create a Bool Expression with an Eq op
     *  A different specialization is provided for each valid T
     */
    template <typename T> BasePtr add(Op::Add::OpContainer &&, AnVec &&);

    /** A specialization of add where T = Expression::BV */
    template <> BasePtr add<Expression::BV>(Op::Add::OpContainer &&operands, AnVec &&av) {

        // For brevity
        namespace Ex = Expression;
        using namespace Simplification;
        using OpC = Op::Add::OpContainer;

        // Or of all operands sym
        bool sym { false };

        // Used for checks
        const Constants::UInt size { dynamic_cast<CTSC<CSized>>(operands[0].get())->size };

        // Checks
        static_assert(std::is_final_v<Ex::BV>, "Create::add's assumes Ex::BV is final");
        Utils::affirm<Error::Expression::Size>(operands.size() >= 2,
                                               "Create::add takes at least 2 operands");
        for (const auto &i : operands) {
            const auto ptr { dynamic_cast<CTSC<CSized>>(i.get()) };
            Utils::affirm<Error::Expression::Type>(
                ptr, "Not all operands given to Create::add<BV> are of type BV");
            Utils::affirm<Error::Expression::Operation>(
                ptr->size == size, "Create::add's arguments are of different sizes");
            // Update sym
            sym |= i->symbolic;
        }

        // Construct expression
        return simplify(
            Ex::factory<Expression::BV>(sym, Op::factory<Op::Add>(std::forward<OpC>(operands)),
                                        std::forward<AnVec>(av), size));
    }

} // namespace Create

#endif
