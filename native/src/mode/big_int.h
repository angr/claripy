/**
 * @file
 * @brief This file defines a macro which defines BigInt modes
 * This exists so it can be used by the C API
 */
#ifndef R_MODE_BIGINT_H_
#define R_MODE_BIGINT_H_

/** A macro defining the internals of BigInt; this is needed for the C API */
#define MODE_BIGINT_VALS(PREFIX) PREFIX##Str = 0, PREFIX##Int

#endif
