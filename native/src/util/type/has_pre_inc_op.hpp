/**
 * @file
 * \ingroup util
 * @brief This file defines a bool that determines if T has the pre ++ operator defined
 */
#ifndef R_UTIL_TYPE_HASPREINCOP_HPP_
#define R_UTIL_TYPE_HASPREINCOP_HPP_

#include "sfinae_test.hpp"

#include "../../constants.hpp"

#include <utility>


namespace Util::Type {

    /** A struct which determines if T has an ++T op defined */
    UTIL_TYPE_SFINAETEST(has_pre_inc_op,      // Invoke this
                         HasPreIncOp,         // Internal class name
                         ++std::declval<U>(), // Condition we are checking
                         typename T           // Template arguments
    )

} // namespace Util::Type

#endif
