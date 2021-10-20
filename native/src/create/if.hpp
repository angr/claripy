/**
 * @file
 * @brief This file defines a method to create an Expr with an Eq Op
 */
#ifndef R_CREATE_IF_HPP_
#define R_CREATE_IF_HPP_

#include "constants.hpp"


namespace Create {

    /** Create an Expr with an If op
     *  Expr pointers may not be nullptr
     */
    template <typename T>
    Expr::BasePtr if_(const Expr::BasePtr &cond, const Expr::BasePtr &left,
                      const Expr::BasePtr &right, Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        namespace Err = Error::Expr;
        using namespace Simplification;

        // Checks
        static_assert(Util::is_ancestor<Ex::Base, T>, "T must subclass Expr::Base");
        Util::affirm<Err::Usage>(cond != nullptr && left != nullptr && right != nullptr,
                                 WHOAMI_WITH_SOURCE " arguments may not be nullptr");
        Util::affirm<Err::Type>(CUID::is_t<T>(left),
                                WHOAMI_WITH_SOURCE "left operand must be a T");

        // Construct expr
        const bool sym { cond->symbolic || left->symbolic || right->symbolic };
        auto op { Op::factory<Op::If>(cond, left, right) };
        if constexpr (Util::is_ancestor<Ex::Bits, T>) {
            return simplify(
                Ex::factory<T>(sym, std::move(op), Ex::get_bit_length(left), std::move(sp)));
        }
        else {
            return simplify(Ex::factory<T>(sym, std::move(op), std::move(sp)));
        }
    }

} // namespace Create

#endif
