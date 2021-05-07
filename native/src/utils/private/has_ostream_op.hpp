/**
 * @file
 * \ingroup utils
 * @brief This file determines a function which checks if T has a << stream op
 */
#ifndef __UTILS_PRIVATE_OHASSTREAMOP_HPP__
#define __UTILS_PRIVATE_OHASSTREAMOP_HPP__

#include "../sfinae_test.hpp"

#include <ostream>


namespace Utils::Private {

    /** A struct which determines if T has a << stream op defined */
    UTILS_SFINAETEST(has_ostream_op,                       // Invoke this
                     HasOStreamOp,                         // Internal class name
                     *static_cast<std::ostream *>(nullptr) // declval is buggy so we cast
                         << std::declval<U>(),             // Condition we are checking
                     typename T                            // Template arguments
    )

} // namespace Utils::Private

#endif
