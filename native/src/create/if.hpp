/**
 * @file
 * @brief This file defines a method to create an Expression with an Eq Op
 */
#ifndef R_CREATE_IF_HPP_
#define R_CREATE_IF_HPP_

#include "constants.hpp"


namespace Create {

    /** Create an Expression with an If op
     *  Expression pointers may not be nullptr
     */
    template <typename T>
    EBasePtr if_(const EBasePtr &cond, const EBasePtr &left, const EBasePtr &right,
                 SPAV &&sp = nullptr) {
        namespace Ex = Expression;
        namespace Err = Error::Expression;
        using namespace Simplification;

        // Type checks
        static_assert(Utils::is_ancestor<Ex::Base, T>, "T must subclass Expression::Base");
        Utils::affirm<Err::Usage>(cond != nullptr && left != nullptr && right != nullptr,
                                  WHOAMI_WITH_SOURCE " arguments may not be nullptr");
        Utils::affirm<Err::Type>(CUID::is_t<T>(left),
                                 WHOAMI_WITH_SOURCE "left operand must be a T");

        // Construct expression
        const bool sym { cond->symbolic || left->symbolic || right->symbolic };
        auto op { Op::factory<Op::If>(cond, left, right) };
        if constexpr (Utils::is_ancestor<Ex::Bits, T>) {
            return simplify(
                Ex::factory<T>(sym, std::move(op), Ex::get_bit_length(left), std::move(sp)));
        }
        else {
            return simplify(Ex::factory<T>(sym, std::move(op), std::move(sp)));
        }
    }

} // namespace Create

#endif
