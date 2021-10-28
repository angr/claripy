/** @file */
#include "make_like.hpp"

#include "../op.hpp"


/** Copy the expr, but use the newly provided annotation vector
 *  in may not be nullptr
 */
Expr::BasePtr Expr::make_like(const Expr::BasePtr &in, Annotation::SPAV &&sp) {
    UTILS_AFFIRM_NOT_NULL_DEBUG(in);
    if (CUID::is_t<Bool>(in)) {
        return ::Expr::factory<Bool>(in->symbolic, Op::BasePtr { in->op }, std::move(sp));
    }
    return factory_cuid(in->cuid, in->symbolic, Op::BasePtr { in->op }, Expr::get_bit_length(in),
                        std::move(sp));
}
