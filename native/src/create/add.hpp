/**
 * @file
 * @brief This file defines a method to create an Expression with an Add Op
 */
#ifndef __CREATE_ADD_HPP__
#define __CREATE_ADD_HPP__

#include "constants.hpp"
#include "private/size.hpp"


namespace Create {

    /** Create a Expression with an Add op */
    inline EBasePtr add(EAnVec &&av, Op::Add::OpContainer &&operands) {

        // For brevity
        namespace Ex = Expression;
        using namespace Simplification;
        using OpC = Op::Add::OpContainer;
        namespace Err = Error::Expression;

        // Get size
        Utils::affirm<Err::Size>(operands.size() >= 2, "Create::add's operands are empty.");
        Utils::affirm<Err::Type>(Ex::is_t<Ex::BV>(operands[0]),
                                 "Create::add operands[0] is not a BV");
        const Constants::UInt size { Private::size(operands[0]) };

        // Calculate simple sym
        bool sym { false };
        for (const auto &i : operands) {
            sym |= i->symbolic;
        }

        // Construct expression
        return simplify(
            Ex::factory<Expression::BV>(std::forward<EAnVec>(av), sym,
                                        Op::factory<Op::Add>(std::forward<OpC>(operands)), size));
    }

} // namespace Create

#endif
