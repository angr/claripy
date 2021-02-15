/**
 * @file
 * @brief This file defines modes for how Expression sizes are computed
 */
#ifndef __CREATE_PRIVATE_SIZEMODE_HPP__
#define __CREATE_PRIVATE_SIZEMODE_HPP__

namespace Create::Private {

    /** Modes that determine how Expression sizes are computed */
    enum class SizeMode {
        /** Not Applicable */
        NA,
        /** First operand's size is selected */
        First,
        /** All operand sizes are summed */
        Add
    };

} // namespace Create::Private

#endif
