/**
 * @file
 * @brief This defines SOC::Concrete
 */
#ifndef __SOC_CONCRETE_HPP__
#define __SOC_CONCRETE_HPP__

#include "base.hpp"


namespace SOC {

    /** A concrete variable */
    struct Concrete : public Base {

        /** Constructor */
        Concrete();

        /** Returns false */
        bool symbolic() const noexcept override final;
    };

} // namespace SOC

#endif
