/**
 * @file
 * @brief This file defines a method to get the size of some T
 */
#ifndef __CREATE_PRIVATE_SIZE_HPP__
#define __CREATE_PRIVATE_SIZE_HPP__

#include "../../expression.hpp"


namespace Create::Private {

    /** Static casts T to Expression::Bits, then returns the size
     *  Warning: This static casts, the user must ensure that p.get() is a T
     */
    inline Constants::UInt size(const Expression::BasePtr &p) noexcept {
        using To = Constants::CTSC<Expression::Bits>;
#ifdef DEBUG
        const auto ptr { dynamic_cast<To>(p.get()) };
        using Err = Utils::Error::Unexpected::BadCast;
        Utils::affirm<Err>(ptr, "Create::Private::size cast failed");
        return ptr->size;
#else
        return static_cast<To>(p.get())->size;
#endif
    }

} // namespace Create::Private

#endif
