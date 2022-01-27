/**
 *  @file
 *  @brief This header defines the C API for Create
 * \ingroup api
 */
#ifndef R_BIG_INT_HPP_
#define R_BIG_INT_HPP_

#include "constants.h"

/** Gets global BigInt mode
 *  @return The current BigInt mode
 */
ClaricppBIM claricpp_big_int_mode_get();

/** Sets the global BigInt mode
 *  @param m The BigInt mode to set the mode to
 *  @return The previous BigInt mode before it was updated
 */
ClaricppBIM claricpp_big_int_mode_set(const ClaricppBIM m);

#endif
