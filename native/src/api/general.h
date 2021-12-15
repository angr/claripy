/**
 * @file
 * @brief This header defines general aspects of the API
 * \ingroup api
 */
#ifndef R_API_GENERAL_H_
#define R_API_GENERAL_H_

#include "callbacks.h"
#include "constants.h"

/** Configures claricpp to be used by python
 *  This does things like change the logging backend
 *  @param py_log The python logging callback the logging system should use
 *  @param py_log The python log level getter callback the logging system should use
 *  @param py_flush The python log flush callback the logging system should use
 */
void claricpp_init_for_python_usage(ClaricppPyLog py_log, ClaricppPyLevel py_lvl,
                                    ClaricppPyFlush py_flush);

/** Returns true if and only if the previous API function failed with an exception
 *  This function will not override the saved exception, on failure the program will crash
 *  @return true if and only if the previous API function failed with an exception
 */
BOOL claricpp_has_exception();

/** Returns the C++ exception Claricpp threw during the previous API function call
 *  This function should only be called if claricpp_has_exception() is true
 *  If this function fails, the failure exception is returned but the saved exception is not cleared
 *  @return The C++ exception Claricpp threw during the previous API function call
 */
ClaricppException claricpp_get_exception();

#endif
