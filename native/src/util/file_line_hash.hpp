/**
 * @file
 * \ingroup util
 * @brief This file defines macro that return a hashes unique to the file (and optionally line)
 */
#ifndef R_UTIL_FILELINEHASH_HPP_
#define R_UTIL_FILELINEHASH_HPP_

#include "norm_path_hash.hpp"


namespace Util {

/** Return a file specific hash */
#define UTILS_FILE_HASH Util::norm_path_hash<Util::strlen(__FILE__)>(__FILE__)

/** Return a file line specific hash */
#define UTILS_FILE_LINE_HASH (UTILS_FILE_HASH + __LINE__)

} // namespace Util

#endif
