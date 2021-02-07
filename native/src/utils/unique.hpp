/**
 * @file
 * \ingroup utils
 * @brief This file defines a unique class gaurnteed to never be used anywhere else
 * Note: The provided macro defines a class unique to the specific line of the specific file
 */
#ifndef __UTILS_UNIQUE_HPP__
#define __UTILS_UNIQUE_HPP__

#include "file_line_hash.hpp"

#include "../constants.hpp"


/** A shortcut for declaring a unique class
 *  This also guarntees that it is unique with respect to other Utils::Unique uses
 */
#define UTILS_DEFINE_UNIQUE                                                                       \
    /** Define a class unique to this line of this file */                                        \
    using Unique = ::Utils::Unique<UTILS_FILE_LINE_HASH>;


namespace Utils {

    /** A unique class */
    template <Constants::UInt> struct Unique final {};

} // namespace Utils

#endif
