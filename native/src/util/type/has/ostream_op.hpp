/**
 * @file
 * \ingroup util
 * @brief This file determines a function which checks if T has a << stream op
 */
#ifndef R_UTIL_TYPE_HAS_OSTREAMOP_HPP_
#define R_UTIL_TYPE_HAS_OSTREAMOP_HPP_

#include "../sfinae_test.hpp"

#include <ostream>


namespace Util::Type::Has {

    /** A struct which determines if T has a << stream op defined */
    UTIL_TYPE_SFINAETEST(ostream_op,                           // Invoke this
                         OStreamOp,                            // Internal class name
                         *static_cast<std::ostream *>(nullptr) // declval is buggy so we cast
                             << std::declval<U>(),             // Condition we are checking
                         typename T                            // Template arguments
    )

} // namespace Util::Type::Has

#endif
