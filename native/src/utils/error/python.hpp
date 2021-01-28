/**
 * @file
 * \ingroup utils
 * @brief This file contains the possible standard python exceptions claricpp can raise
 * These exceptions have python analogs and must be caught and set to python
 * via a different method.
 * Note: these exceptions ignore the rule of 5 (see claricpp.hpp)
 * @todo Document method when known
 */
#ifndef __ERRORS_PYTHON_HPP__
#define __ERRORS_PYTHON_HPP__

#include "claricpp.hpp"


namespace Utils::Error {

    // Exceptions that should be passed back to python
    namespace Python {

        /** Base Python exception
         *  All Python exceptions must derive from this
         */
        struct Base : public Claricpp {

            /** Inherit constructors */
            using Claricpp::Claricpp;

            /** Virtual destructor */
            virtual ~Base();
        };

        /** Analogous to python's ValueError exception */
        DEFINE_SUBCLASS_WITH_CTOR(ValueError, Base)

    } // namespace Python

} // namespace Utils::Error

#endif
