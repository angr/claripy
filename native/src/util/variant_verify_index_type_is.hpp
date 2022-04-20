/**
 * @file
 * \ingroup util
 * @brief This file defines a macro to verify the type of a variant index
 */
#ifndef R_SRC_UTIL_VARIANTVERIFYINDEXTYPEIS_HPP_
#define R_SRC_UTIL_VARIANTVERIFYINDEXTYPEIS_HPP_

#include <type_traits>
#include <variant>


/** Verifies that index INDEX of variant VAR is of type TYPE, ignoring the variant's consts */ // @
#define UTIL_VARIANT_VERIFY_INDEX_TYPE_IGNORE_CONST(VAR, INDEX, TYPE)                              \
    static_assert(                                                                                 \
        std::is_same_v<                                                                            \
            TYPE, std::remove_const_t<std::remove_reference_t<decltype(std::get<INDEX>((VAR)))>>>, \
        "Wrong index for given type");


#endif
