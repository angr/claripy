/**
 * @file
 * @brief This defines SOC::Base
 */
#ifndef __SOC_BASE_HPP__
#define __SOC_BASE_HPP__

#include "../hash.hpp"

#include <cstddef>
#include <functional>


namespace SOC {

    /** A class representing either a symbolic or concrete variable
     *  Note: the factory demands a static hash function that takes the
     *  same arguments as the constructor except by const reference
     */
    struct Base : public Hash::Hashed {

        /** Returns true if this is symbolic */
        virtual bool symbolic() const noexcept = 0;

      protected:
        /** Passthrough constructor */
        explicit inline Base(const Hash::Hash &h) noexcept : Hash::Hashed { h } {}

        /** Virtual destructor */
        virtual inline ~Base() noexcept override = 0;

        // Rule of 5
        SET_IMPLICITS_CONST_MEMBERS(Base, default, noexcept)
    };

    /** Default virtual destructor */
    Base::~Base() noexcept = default;

} // namespace SOC

#endif
