/**
 * @file
 * @brief This file defines a method to copy an expression but change the annotations
 */
#ifndef R_EXPRESSION_COPY_HPP_
#define R_EXPRESSION_COPY_HPP_

#include "base.hpp"
#include "factory.hpp"
#include "instantiables.hpp"


namespace Expression {

    /** Copy the expression, but use the newly provided annotation vector
     *  in may not be nullptr
     */
    inline Expression::BasePtr copy(const Expression::BasePtr &in, Base::SPAV &&sp) {
        UTILS_AFFIRM_NOT_NULL_DEBUG(in);
        auto op { in->op };
        switch (in->cuid) {
            case Bool::static_cuid:
                return ::Expression::factory<Bool>(in->symbolic, std::move(op), std::move(sp));
/** A local macro used for consistency */
#define BITS_SUB(TYPE)                                                                            \
    case TYPE::static_cuid:                                                                       \
        return ::Expression::factory<TYPE>(in->symbolic, std::move(op),                           \
                                           Expression::get_bit_length(in), std::move(sp));
                BITS_SUB(String);
                BITS_SUB(FP);
                BITS_SUB(VS);
                BITS_SUB(BV);
// Cleanup
#undef BITS_SUB
            // Should never be hit
            default:
                throw Utils::Error::Unexpected::Unknown(WHOAMI_WITH_SOURCE,
                                                        "given an unknown cuid");
        }
    }

} // namespace Expression

#endif
