/**
 * @file
 * @brief This file defines a method to create an Expr with an Eq Op
 */
#ifndef R_SRC_CREATE_IF_HPP_
#define R_SRC_CREATE_IF_HPP_

#include "constants.hpp"


namespace Create {

    /** Create an Expr with an If op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr if_(const Expr::BasePtr &cond, const Expr::BasePtr &left,
                             const Expr::BasePtr &right, Expr::OpPyDict d = {}) {
        UTIL_ASSERT(Error::Expr::Usage, cond && left && right, "arguments may not be nullptr");
        const bool sym { cond->symbolic || left->symbolic || right->symbolic };
        using Simplify::simplify;
        if (CUID::is_t<Expr::Bool>(left)) {
            return simplify(Expr::factory<Expr::Bool>(sym, Op::factory<Op::If>(cond, left, right),
                                                      std::move(d)));
        }
        return simplify(Expr::factory_cuid(left->cuid, sym, Op::factory<Op::If>(cond, left, right),
                                           std::move(d), Expr::bit_length(left)));
    }

} // namespace Create

#endif
