/**
 * @file
 * \ingroup utils
 * @brief This file contains the possible standard python exceptions claricpp can raise
 * These exceptions have python analogs and must be caught and set to python
 * via a different method.
 * @todo Document method when known
 */
#ifndef __UTILS_ERROR_PYTHON_HPP__
#define __UTILS_ERROR_PYTHON_HPP__

#include "claricpp.hpp"


namespace Utils::Error::Python {

    /** Base Python exception
     *  All Python exceptions must derive from this
     */
    DEFINE_NONFINAL_EXCEPTION(Base, Claricpp);

    /** A custom claripy exception
     *  All Claripy exceptions must derive from this
     */
    DEFINE_NONFINAL_EXCEPTION(Claripy, Base);

    /** Analogous to python's ValueError exception */
    DEFINE_FINAL_EXCEPTION(ValueError, Base);

} // namespace Utils::Error::Python

#endif
