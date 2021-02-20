/**
 * @file
 * \ingroup utils
 * @brief This file contains the possible standard python exceptions claricpp can raise
 * These exceptions have python analogs and must be caught and set to python
 * via a different method.
 * Note: these exceptions ignore the rule of 5 (see claricpp.hpp)
 * @todo Document method when known
 */
#ifndef __UTILS_ERROR_PYTHON_HPP__
#define __UTILS_ERROR_PYTHON_HPP__

#include "claricpp.hpp"


namespace Utils::Error {

    // Exceptions that should be passed back to python
    namespace Python {

        /** Base Python exception
         *  All Python exceptions must derive from this
         */
        DEFINE_NONFINAL_INSTANTIABLE_SUBCLASS_WITH_CTOR(Base, Claricpp)

        /** A custom claripy exception
         *  All Claripy exceptions must derive from this
         */
        DEFINE_NONFINAL_INSTANTIABLE_SUBCLASS_WITH_CTOR(Claripy, Base)

        /** Analogous to python's ValueError exception */
        DEFINE_FINAL_SUBCLASS_WITH_CTOR(ValueError, Base)

    } // namespace Python

} // namespace Utils::Error

#endif
