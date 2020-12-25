/**
 * @file
 * @brief This file defines the cout logging backend
 */
#ifndef __UTILS_LOG_BACKEND_COUT_HPP__
#define __UTILS_LOG_BACKEND_COUT_HPP__

#include "ostream.hpp"

#include <ostream>


namespace Utils::Log::Backend {

    /** The stream backend
     *  This takes in an ostream and logs to it
     */
    struct Cout : public OStream {

        /** Constructor */
        Cout();
    };

} // namespace Utils::Log::Backend

#endif
