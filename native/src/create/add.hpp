/**
 * @file
 * @brief This file defines a method to create an Expression with an Add Op
 */
#ifndef __CREATE_ADD_HPP__
#define __CREATE_ADD_HPP__

#include "constants.hpp"


namespace Create {

    /** Create a Expression with an Add op */
    inline EBasePtr add(EAnVec &&av, Op::Add::OpContainer &&operands) {

        // For brevity
        namespace Ex = Expression;
        using namespace Simplification;
        using OpC = Op::Add::OpContainer;
        namespace Err = Error::Expression;

        // Or of all operands sym
        bool sym { false };

        // Checks
        static_assert(std::is_final_v<Ex::BV>, "Create::add's assumes Expression::BV is final");
        Utils::affirm<Err::Size>(operands.size() >= 1, "Create::add's operands are empty.");

        // Verify that Op::Add is flat and that the first operand is of type BV
        // Flat ops promise to verify all operand types are identical
        static_assert(Utils::is_ancestor<Op::FlatBase, Op::Add>,
                      "Op::Add is not flat as expected");
        Utils::affirm<Err::Type>(
            operands[0]->cuid == Expression::BV::static_cuid,
            "Create::add operands are not all of type Expression::BV as is required.");

        // Get size
        // We already verified that operands[0] is a BV
        static_assert(Utils::is_ancestor<CSized, Expression::BV>, "BV is unsized");
        const Constants::UInt size { static_cast<CTS<Expression::BV>>(operands[0].get())->size };

        // Verify identical sizes
        for (const auto &i : operands) {
            const auto ptr { dynamic_cast<CTSC<CSized>>(i.get()) };
            Utils::affirm<Err::Type>(ptr,
                                     "Not all operands given to Create::add<BV> are of type BV");
            Utils::affirm<Err::Operation>(ptr->size == size,
                                          "Create::add's arguments are of different sizes");
            // Update sym
            sym |= i->symbolic;
        }

        // Construct expression
        return simplify(
            Ex::factory<Expression::BV>(std::forward<EAnVec>(av), sym,
                                        Op::factory<Op::Add>(std::forward<OpC>(operands)), size));
    }

} // namespace Create

#endif
