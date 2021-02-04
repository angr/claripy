/**
 * @file
 * @brief This file defines the base op class
 */
#ifndef __OP_BASE_HPP__
#define __OP_BASE_HPP__

#include "macros.hpp" // For subclasses

#include "../factory.hpp"


namespace Op {

    /** Base operation expression
     *  All op expressions must subclass this
     */
    class Base : public Factory::FactoryMade {
        FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(Base)
      protected:
        /** Constructor */
        explicit inline Base(const Hash::Hash &h, const Constants::UInt cuid_) noexcept
            : FactoryMade { h, cuid_ } {}

        /** Virtual destructor */
        inline ~Base() noexcept override = 0;

        // Disable other methods of construction
        SET_IMPLICITS_CONST_MEMBERS(Base, delete)
    };

    /** Default virtual destructor */
    Base::~Base() noexcept = default;

} // namespace Op


#endif
