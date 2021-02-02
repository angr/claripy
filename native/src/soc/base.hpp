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
      protected:
        /** Passthrough constructor */
        inline Base(const Hash::Hash &h) : Hash::Hashed { h } {}

      public:
        /** Returns true if this is symbolic */
        virtual bool symbolic() const noexcept = 0;
    };

} // namespace SOC

#endif
