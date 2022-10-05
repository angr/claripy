/**
 * @file
 * @brief This file contains the possible Backend exceptions claricpp can raise
 * These exceptions have python analogs and must be caught and set to python
 * via a different method.
 * @todo Document method when known
 */
#ifndef R_SRC_ERROR_BACKEND_HPP_
#define R_SRC_ERROR_BACKEND_HPP_

#include "../util.hpp"


namespace Error::Backend {

    /** Claripy Expr exception */
    using Claripy = Util::Err::Python::Claripy;

    // Final classes

    /** @todo document */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(Abstraction, Claripy);

    /** @todo document */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(Unsupported, Claripy);

    /** Thrown when a backend solver was interrupted */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(SolverInterrupt, Claripy);

} // namespace Error::Backend

#endif
