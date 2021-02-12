/**
 * @file
 * @brief This file defines a method to get the size of some T
 */
#ifndef __CREATE_PRIVATE_SIZE_HPP__
#define __CREATE_PRIVATE_SIZE_HPP__

#include "../../expression.hpp"


namespace Create::Private {

    /** Static casts T to Expression::Bits, then returns the size */
    Constants::UInt size(const Expression::BasePtr &p) noexcept {
        using Err = Utils::Error::Unexpected::BadCast;
        using namespace Expression;
        using namespace Constants;
#ifdef DEBUG
        const auto ptr { dynamic_cast<CTSC<BV>>(p.get()) };
        Utils::affirm<Err>(ptr, "Create::Private::size cast failed");
        return ptr->size;
#else
        return static_cast<CTSC<BV>>(p.get())->size;
#endif
    }

} // namespace Create::Private

#endif
