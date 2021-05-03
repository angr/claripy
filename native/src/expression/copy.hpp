/**
 * @file
 * @brief This file defines a method to copy an expression but change the annotations
 */
#ifndef __EXPRESSION_COPY_HPP__
#define __EXPRESSION_COPY_HPP__

#include "base.hpp"
#include "factory.hpp"
#include "instantiables.hpp"


namespace Expression {

    /** Copy the expression, but use the newly provided annotation vector */
    inline Expression::BasePtr copy(const Expression::BasePtr &in, Base::AnVec &&ans) {
        auto op { in->op };
        switch (in->cuid) {
            case Bool::static_cuid:
                return ::Expression::factory<Bool>(std::move(ans), in->symbolic, std::move(op));
/** A local macro used for consistency */
#define BITS_SUB(TYPE)                                                                            \
    case TYPE::static_cuid:                                                                       \
        return ::Expression::factory<TYPE>(                                                       \
            std::move(ans), in->symbolic, std::move(op),                                          \
            Utils::checked_static_cast<Constants::CTSC<Bits>>(in.get())->bit_length);
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
