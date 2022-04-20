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
                             const Expr::BasePtr &right, Annotation::SPAV sp = empty_spav) {
        using namespace Simplify;
        UTIL_ASSERT(Error::Expr::Usage, cond != nullptr && left != nullptr && right != nullptr,
                    "arguments may not be nullptr");
        const bool sym { cond->symbolic || left->symbolic || right->symbolic };
        if (CUID::is_t<Expr::Bool>(left)) {
            return simplify(Expr::factory<Expr::Bool>(sym, Op::factory<Op::If>(cond, left, right),
                                                      std::move(sp)));
        }
        return simplify(Expr::factory_cuid(left->cuid, sym, Op::factory<Op::If>(cond, left, right),
                                           Expr::get_bit_length(left), std::move(sp)));
    }

} // namespace Create

#endif
