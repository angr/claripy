/**
 * @file
 * @brief This file methods for accessing the log style
 */
#ifndef __UTILS_LOG_STYLE_ACCESS_HPP__
#define __UTILS_LOG_STYLE_ACCESS_HPP__

#include "abstract_base.hpp"


/** A namespace used for the utils directory */
namespace Utils::Log::Style {

    /** Set the logging style by copy */
    void set(AbstractBase s);

    /** Return a copy of the style */
    AbstractBase get();

} // namespace Utils::Log::Style

#endif
