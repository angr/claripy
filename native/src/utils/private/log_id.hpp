/**
 * @file
   @brief This file defines Utils::LogID
 */
#ifndef __UTILS_PRIVATE_LOGID_HPP__
#define __UTILS_PRIVATE_LOGID_HPP__

#include "../../macros.hpp"
#include "../inc.hpp"


/** A namespace used for the utils directory */
namespace Utils {

    /** A namespace used to designate certain items in utils as private
     *  These functions should not be called outside of the utils directory
     *  This is useful for helper functions templated functions call
     */
    namespace Private {

        /** Assign a different value to each log type */
        template <typename T> Constants::Int LogID() {
            const static Constants::Int id = inc<T>();
            return id;
        }

    } // namespace Private

} // namespace Utils

#endif
