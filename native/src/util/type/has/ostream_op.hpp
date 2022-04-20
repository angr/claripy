/**
 * @file
 * \ingroup util
 * @brief This file determines a function which checks if T has a << stream op
 */
#ifndef R_SRC_UTIL_TYPE_HAS_OSTREAMOP_HPP_
#define R_SRC_UTIL_TYPE_HAS_OSTREAMOP_HPP_

#include "../sfinae_test.hpp"

#include <ostream>


namespace Util::Type::Has {

    /** A struct which determines if T has a << stream op defined */
    UTIL_TYPE_SFINAETEST(ostream_op,                                        // Name
                         std::declval<std::ostream>() << std::declval<T>(), // Condition
                         typename T                                         // Template arguments
    )

} // namespace Util::Type::Has

#endif
