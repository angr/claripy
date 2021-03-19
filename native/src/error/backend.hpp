/**
 * @file
 * @brief This file contains the possible Backend exceptions claricpp can raise
 * These exceptions have python analogs and must be caught and set to python
 * via a different method.
 * @todo Document method when known
 */
#ifndef __ERROR_BACKEND_HPP__
#define __ERROR_BACKEND_HPP__

#include "../utils.hpp"


namespace Error {

    // Expression errors
    namespace Backend {

        /** Claripy Expression exception */
        using Claripy = Utils::Error::Python::Claripy;

        /** @todo document */
        DEFINE_FINAL_SUBCLASS_WITH_CTOR(Base, Claripy)

    } // namespace Backend

} // namespace Error

#endif
