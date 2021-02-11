/**
 * @file
 * \ingroup utils
 * @brief This file defines a bool that determines if T has the pre ++ operator defined
 */
#ifndef __UTILS_PRIVATE_HASPREINCOP_HPP__
#define __UTILS_PRIVATE_HASPREINCOP_HPP__

#include "../../constants.hpp"
#include "../sfinae_test.hpp"

#include <utility>

namespace Utils::Private {

    /** A struct which determines if T has a << stream op defined */
    UTILS_SFINAETEST(has_pre_inc_op,      // Invoke this
                     HasPreIncOp,         // Internal class name
                     ++std::declval<U>(), // Condition we are checking
                     typename T           // Template arguments
    )

} // namespace Utils::Private

#endif
