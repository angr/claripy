/**
 * @file
 * \ingroup util
 * @brief This file contains the possible standard python exceptions claricpp can raise
 * These exceptions have python analogs and must be caught and set to python
 * via a different method.
 * @todo Document method when known
 */
#ifndef R_UTIL_ERROR_PYTHON_HPP_
#define R_UTIL_ERROR_PYTHON_HPP_

#include "claricpp.hpp"


namespace Util::Error::Python {

    /** Base Python exception
     *  All Python exceptions must derive from this
     */
    DEFINE_NONFINAL_EXCEPTION(Base, Claricpp);

    /** A custom claripy exception
     *  All Claripy exceptions must derive from this
     */
    DEFINE_NONFINAL_EXCEPTION(Claripy, Base);

    /** Analogous to python's ValueError exception */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(ValueError, Base);

} // namespace Util::Error::Python

#endif
