/**
 * @file
 * @brief This header defines callback signatures for FFI Python callbacks
 * \ingroup api
 */
#ifndef R_API_CALLBACKS_H_
#define R_API_CALLBACKS_H_

#include "constants.h"


/** The log callback type */
typedef void (*const ClaricppPyLog)(PyStr, const ClaricppLogLvl, PyStr);

/** The level getter callback type */
typedef ClaricppLogLvl (*const ClaricppPyLevel)(PyStr);


#endif
