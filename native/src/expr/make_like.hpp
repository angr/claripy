/**
 * @file
 * @brief This file defines a method to copy an expr but change the annotations
 */
#ifndef R_EXPR_MAKELIKE_HPP_
#define R_EXPR_MAKELIKE_HPP_

#include "base.hpp"
#include "factory.hpp"
#include "instantiables.hpp"


namespace Expr {

    /** Copy the expr, but use the newly provided annotation vector
     *  in may not be nullptr
     */
    inline Expr::BasePtr make_like(const Expr::BasePtr &in, Annotation::SPAV &&sp) {
        UTILS_AFFIRM_NOT_NULL_DEBUG(in);
        if (in->cuid == Bool::static_cuid) {
            return ::Expr::factory<Bool>(in->symbolic, Op::BasePtr { in->op }, std::move(sp));
        }
        return factory_cuid(in->cuid, in->symbolic, Op::BasePtr { in->op },
                            Expr::get_bit_length(in), std::move(sp));
    }

} // namespace Expr

#endif
