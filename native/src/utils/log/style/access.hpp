/**
 * @file
 * @brief This file methods for accessing the Log Style
 */
#ifndef __UTILS_LOG_STYLE_ACCESS_HPP__
#define __UTILS_LOG_STYLE_ACCESS_HPP__

#include "abstract_base.hpp"


namespace Utils::Log::Style {

    /** Set the logging style by copy */
    void set(AbstractBase s);

    /** Return a copy of the style */
    AbstractBase get();

} // namespace Utils::Log::Style

#endif
