/**
 * @file
 * @brief This defines SOC::Symbolic
 */
#ifndef __SOC_SYMBOLIC_HPP__
#define __SOC_SYMBOLIC_HPP__

#include "base.hpp"

#include <string>


namespace SOC {

    /** A symbolic variable */
    struct Symbolic : public Base {

        /** Constructor */
        Symbolic(const std::string &name);

        /** Returns true */
        bool symbolic() const noexcept override final;

        /** The name of the symbol */
        const std::string name;
    };

} // namespace SOC

#endif
