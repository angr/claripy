/**
 * @file
 * \ingroup utils
 * @brief This file defines a macro to verify the type of a variant index
 */
#ifndef R_UTILS_VARIANTINDEXTYPEIS_HPP_
#define R_UTILS_VARIANTINDEXTYPEIS_HPP_

#include <type_traits>
#include <variant>


#define UTILS_VARIANT_VERIFY_INDEX_TYPE(VAR, INDEX, TYPE)                                         \
    static_assert(std::is_same_v<const TYPE &, decltype(std::get<INDEX>((VAR)))>,                 \
                  "Wrong index for given type");


#endif
