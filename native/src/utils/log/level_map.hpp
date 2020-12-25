/**
 * @file
 * @brief This file defines a map from the Utils::Log::Level's to their string representations
 */
#ifndef __UTILS_LOG_LEVELMAP_HPP__
#define __UTILS_LOG_LEVELMAP_HPP__

#include "level.hpp"

#include "../../constants.hpp"

#include <map>


namespace Utils::Log {

    /** A map that maps a Level enum to its name */
    const extern std::map<Level, Constants::CCSC> level_map;

} // namespace Utils::Log

#endif
