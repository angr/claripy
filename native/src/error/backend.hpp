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
    DEFINE_NONFINAL_EXCEPTION(Base, Claripy);

    // Final classes

    /** @todo document */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(Abstraction, Base);

    /** @todo document */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(Unsupported, Base);

    /** @todo document */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(VSA, Base);

    /** @todo document */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(Z3, Claripy);

    /** @todo document */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(MissingSolver, Claripy);

} // namespace Error::Backend

#endif
