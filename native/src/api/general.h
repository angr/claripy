/**
 * @file
 * @brief This header defines general aspects of the API
 * \ingroup api
 */
#ifndef R_API_GENERAL_HPP_
#define R_API_GENERAL_HPP_

#include "constants.h"

/** Configures claricpp to be used by python
 *  This does things like change the logging backend
 */
void claricpp_init_for_python_usage();

/** Returns true if and only if the previous API function failed with an exception
 *  If this fails, the program will crash as we have no way of functionally using claricpp
 *  @return true if and only if the previous API function failed with an exception
 */
BOOL claricpp_has_exception();

/** Returns the C++ exception Claricpp threw during the previous API function call
 *  This function should only be called if claricpp_has_exception() is true
 *  If this function fails, the failire exception is returned but the saved exception is not cleared
 *  @return The C++ exception Claricpp threw during the previous API function call
 */
ClaricppException claricpp_get_exception();

#endif // R_GENERAL_HPP_
