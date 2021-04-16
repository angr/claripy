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


namespace Error::Backend {

    /** Claripy Expression exception */
    using Claripy = Utils::Error::Python::Claripy;

    // Intermediate classes

    /** Expression Balance exception */
    DEFINE_NONFINAL_EXCEPTION(Base, Claripy);

    // Final classes

    /** @todo document */
    DEFINE_FINAL_EXCEPTION(Unsupported, Base);

    /** @todo document */
    DEFINE_FINAL_EXCEPTION(VSA, Base);

    /** @todo document */
    DEFINE_FINAL_EXCEPTION(Z3, Claripy);

    /** @todo document */
    DEFINE_FINAL_EXCEPTION(MissingSolver, Claripy);

} // namespace Error::Backend

#endif
