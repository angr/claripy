/**
 * @file
 * \ingroup api
 */
#include "api.h"

/* This file is intentionally empty, it serves 2 purposes:

1. It forces api.h to only contain C, since the compiler will compile this file for C
	Note: extern "C" does might wiggle room that this might not
2. It exists to allow CMake to easily gcc -E api.h for the python bindings

End of file */
