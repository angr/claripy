/**
 * @file
 * @brief This file defines the base op class
 */
#ifndef __OP_BASE_HPP__
#define __OP_BASE_HPP__

#include "macros.hpp" // For subclasses

#include "../cuid.hpp"
#include "../hash.hpp"


namespace Op {

    /** Base operation expression
     *  All op expressions must subclass this
     */
    class Base : public Hash::Hashed, public CUID {
      protected:
        /** Constructor */
        explicit inline Base(const Hash::Hash &h, const Constants::UInt cuid) noexcept
            : Hashed { h }, CUID { cuid } {}

        /** Virtual destructor */
        inline ~Base() noexcept override = 0;

        // Disable other methods of construction
        SET_IMPLICITS_CONST_MEMBERS(Base, delete)
    };

    /** Default virtual destructor */
    Base::~Base() noexcept = default;

} // namespace Op


#endif
