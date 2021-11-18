/**
 * @file
 * \ingroup util
 * @brief This file defines a bool that determines if T has the pre ++ operator defined
 */
#ifndef R_UTIL_TYPE_HAS_PREINCOP_HPP_
#define R_UTIL_TYPE_HAS_PREINCOP_HPP_

#include "../sfinae_test.hpp"

#include <utility>


namespace Util::Type::Has {

    /** A struct which determines if T has an ++T op defined */
    UTIL_TYPE_SFINAETEST(pre_inc_op,          // Invoke this
                         PreIncOp,            // Internal class name
                         ++std::declval<U>(), // Condition we are checking
                         typename T           // Template arguments
    )

} // namespace Util::Type::Has

#endif
