/**
 * @file
 * \ingroup utils
 * @brief This file defines UTILS_TYPE_PUN and related macros
 * We use this instead of unions as unions can have undefined behavior when type punning.
 * Likewise, due to 'strict anti-aliasing' rules, type punning via casting can have
 * undefined behavior, especially with -O2 or higher level optimizations.
 */
#ifndef R_UTILS_TYPEPUN_HPP_
#define R_UTILS_TYPEPUN_HPP_

#include "declare.hpp"

#include "../macros.hpp"

#include <cstring>


/** Type puns IN_OBJ onto OUT_ONTO_PTR of type (& OUT_TYPE). IS_ARRAY should be true if IN_OBJ is
 *  not a pointer to a single object but rather to an array containing multiple objects that
 *  should collectively be read while type-punning to the out type.
 *  This is a safe way to type pun in C++ provided that the Out type is well formed no matter
 *  what arrangement of bits its representation has. For example, ints are safe, doubles are
 *  not since they have some undefined forms. In this case, it is up to the user to ensure
 *  that the arrangement of bits resulting from the pun leads to a valid representation
 *  of the type being punned to.
 *  Warning: If IS_ARRAY is true, it is the programmer's job to ensure that IN_OBJ's pointed
 *  to data is large enough to pun to a OUT_TYPE. IS_ARRAY is simply a sanity check.
 */
#define UTILS_TYPE_PUN_ONTO(OUT_TYPE, OUT_ONTO_PTR, IN_OBJ, IS_ARRAY)                             \
    static_assert((IS_ARRAY) || (sizeof(OUT_TYPE) <= sizeof(*(IN_OBJ))),                          \
                  "cannot pun to a size larger than the input object");                           \
    /* Not memmove since compilers seem to be more capable of no-op-ing memcpy with -O3 */        \
    std::memcpy((OUT_ONTO_PTR), (IN_OBJ), sizeof(OUT_TYPE));


#endif
