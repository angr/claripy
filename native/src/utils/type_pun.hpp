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

/** Type puns IN_OBJ onto a new OUT_TYPE named OUT_NAME. IS_ARRAY should be true if IN_OBJ is not
 *  a pointer to a single object but rather to an array containing multiple objects that should
 *  collectively be read while type-punning to the out type.
 *  This is a safe way to type pun in C++ provided that the Out type is well formed no matter
 *  what arrangement of bits its representation has. For example, ints are safe, doubles are
 *  not since they have some undefined forms. In this case, it is up to the user to ensure
 *  that the arrangement of bits resulting from the pun leads to a valid representation
 *  of the type being punned to. UNIQUE will be used as part of an internal variable name; this
 *  set it as needed to avoid any name collisions with other parts of the code in scope.
 *  Warning: If IS_ARRAY is true, it is the programmer's job to ensure that IN_OBJ's pointed
 *  to data is large enough to pun to a OUT_TYPE. IS_ARRAY is simply a sanity check.
 */
#define UTILS_TYPE_PUN(OUT_TYPE, OUT_NAME, IN_OBJ, IS_ARRAY, UNIQUE)                              \
    Utils::Declare<OUT_TYPE, true> MACRO_CONCAT(_tpi##IS_ARRAY, __LINE__);                        \
    /* Due to the newline escapes, this entire macro has the same __LINE__ value */               \
    OUT_TYPE &OUT_NAME { MACRO_CONCAT(_tpi##IS_ARRAY, __LINE__).value };                          \
    UTILS_TYPE_PUN_ONTO(OUT_TYPE, &OUT_NAME, (IN_OBJ), (IS_ARRAY));

/** Type puns IN_OBJ onto a new OUT_TYPE named OUT_NAME. IS_ARRAY should be true if IN_OBJ is not
 *  a pointer to a single object but rather to an array containing multiple objects that should
 *  collectively be read while type-punning to the out type.
 *  This is a safe way to type pun in C++ provided that the Out type is well formed no matter
 *  what arrangement of bits its representation has. For example, ints are safe, doubles are
 *  not since they have some undefined forms. In this case, it is up to the user to ensure
 *  that the arrangement of bits resulting from the pun leads to a valid representation
 *  of the type being punned to.
 *  Warning: This defaults UNIQUE to _, if you typepun multiple things within the same scope
 *  you may run into name collisions.
 *  Warning: If IS_ARRAY is true, it is the programmer's job to ensure that IN_OBJ's pointed
 *  to data is large enough to pun to a OUT_TYPE. IS_ARRAY is simply a sanity check.
 */
#define UTILS_TYPE_PUN_(OUT_TYPE, OUT_NAME, IN_OBJ, IS_ARRAY)                                     \
    UTILS_TYPE_PUN(OUT_TYPE, OUT_NAME, (IN_OBJ), IS_ARRAY, _);


#endif
