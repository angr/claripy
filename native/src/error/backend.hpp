/**
 * @file
 * @brief This file contains the possible Backend exceptions claricpp can raise
 * These exceptions have python analogs and must be caught and set to python
 * via a different method.
 * @todo Document method when known
 */
#ifndef R_ERROR_BACKEND_HPP_
#define R_ERROR_BACKEND_HPP_

#include "../util.hpp"


namespace Error::Backend {

    /** Claripy Expr exception */
    using Claripy = Util::Err::Python::Claripy;

    // Intermediate classes

    /** Expr Balance exception */
    UTIL_ERR_DEFINE_NONFINAL_EXCEPTION(Base, Claripy);

    // Final classes

    /** @todo document */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(Abstraction, Base);

    /** @todo document */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(Unsupported, Base);

    /** @todo document */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(VSA, Base);

    /** @todo document */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(Z3, Claripy);

    /** @todo document */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(MissingSolver, Claripy);

} // namespace Error::Backend

#endif
