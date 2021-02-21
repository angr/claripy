/**
 * @file
 * @brief This file defines a method to get the bit length of some T
 */
#ifndef __CREATE_PRIVATE_BITLENGTH_HPP__
#define __CREATE_PRIVATE_BITLENGTH_HPP__

#include "../../expression.hpp"


namespace Create::Private {

    /** Static casts T to Expression::Bits, then returns the bit_length
     *  Warning: This static casts, the user must ensure that p.get() is a T
     */
    inline Constants::UInt bit_length(const Expression::BasePtr &p) noexcept {
        using To = Constants::CTSC<Expression::Bits>;
#ifdef DEBUG
        const auto ptr { dynamic_cast<To>(p.get()) };
        using Err = Utils::Error::Unexpected::BadCast;
        Utils::affirm<Err>(ptr, WHOAMI_WITH_SOURCE "cast failed");
        return ptr->bit_length;
#else
        return static_cast<To>(p.get()) - bit_length;
#endif
    }

} // namespace Create::Private

#endif
