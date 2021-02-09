/**
 * @file
 * @brief This file defines the base op class
 */
#ifndef __OP_BASE_HPP__
#define __OP_BASE_HPP__

#include "macros.hpp"

#include "../factory.hpp"


namespace Op {

    /** Base operation expression
     *  All op expressions must subclass this
     */
    class Base : public Factory::FactoryMade {
        OP_PURE_INIT(Base)
      protected:
        /** Protected constructor */
        explicit inline Base(const Hash::Hash &h, const CUID::CUID &cuid_) noexcept
            : FactoryMade { h, cuid_ } {}
    };

    /** Default virtual destructor */
    Base::~Base() noexcept = default;

} // namespace Op


#endif
