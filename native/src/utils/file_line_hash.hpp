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
#define FILEHASH Utils::fnv1a(__FILE__, strlen(__FILE__))

/** Return a file line specific hash */
#define FILELINEHASH (FILEHASH + __LINE__)

} // namespace Utils

#endif
