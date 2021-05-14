/**
 * @file
 * @brief This file defines a method to create an Expression with an Eq Op
 */
#ifndef R_CREATE_IF_HPP_
#define R_CREATE_IF_HPP_

#include "constants.hpp"


namespace Create {

    /** Create an Expression with an If op */
    template <typename T>
    EBasePtr if_(EAnVec &&av, const EBasePtr &cond, const EBasePtr &left, const EBasePtr &right) {

        // For brevity
        namespace Ex = Expression;
        namespace Err = Error::Expression;
        using namespace Simplification;

        // Type checks
        static_assert(Utils::is_ancestor<Expression::Base, T>, "T must subclass Expression::Base");
        Utils::affirm<Err::Type>(CUID::is_t<T>(left),
                                 WHOAMI_WITH_SOURCE "left operand must be a T");

        // Construct expression
        const bool sym { cond->symbolic || left->symbolic || right->symbolic };
        auto op { Op::factory<Op::If>(cond, left, right) };
        if constexpr (Utils::is_ancestor<Expression::Bits, T>) {
            return simplify(Ex::factory<T>(std::forward<EAnVec>(av), sym, std::move(op),
                                           Expression::get_bit_length(left)));
        }
        else {
            return simplify(Ex::factory<T>(std::forward<EAnVec>(av), sym, std::move(op)));
        }
    }

} // namespace Create

#endif
