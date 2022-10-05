/**
 * @file
 * \ingroup util
 * @brief This file contains the possible standard python exceptions claricpp can raise
 * These exceptions have python analogs and must be caught and set to python
 * via a different method.
 * @todo Document method when known
 */
#ifndef R_SRC_UTIL_ERR_PYTHON_HPP_
#define R_SRC_UTIL_ERR_PYTHON_HPP_

#include "claricpp.hpp"


namespace Util::Err::Python {

    /** Base Python exception
     *  All Python exceptions must derive from this
     */
    UTIL_ERR_DEFINE_NONFINAL_EXCEPTION(Base, Claricpp);

    /** A custom claripy exception
     *  All Claripy exceptions must derive from this
     */
    UTIL_ERR_DEFINE_NONFINAL_EXCEPTION(Claripy, Base);

    /** A custom claripy exception for python runtime errors */
    UTIL_ERR_DEFINE_NONFINAL_EXCEPTION(Runtime, Base);

    /** A custom claripy exception for python keyboard interrupts */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(KeyboardInterrupt, Base);

} // namespace Util::Err::Python

#endif
