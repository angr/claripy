/**
 * @file
 * \ingroup utils
 * @brief This file defines macro that return a hashes unique to the file (and optionally line)
 */
#ifndef __UTILS_FILELINEHASH_HPP__
#define __UTILS_FILELINEHASH_HPP__

#include "fnv1a.hpp"
#include "strlen.hpp"


namespace Utils {

/** Return a file specific hash */
#define UTILS_FILE_HASH Utils::fnv1a<Constants::UInt>(__FILE__, Utils::strlen(__FILE__))

/** Return a file line specific hash
 */
#define UTILS_FILE_LINE_HASH (UTILS_FILE_HASH + __LINE__)

} // namespace Utils

#endif
