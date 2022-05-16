/**
 * @file
 * @brief This file defines a class that has a repr function
 */
#ifndef R_SRC_HASREPR_HPP_
#define R_SRC_HASREPR_HPP_

#include "macros.hpp"

#include <sstream>

/** A struct with a repr function; subclasses must define repr_stream
 *  This function follows the design pattern: CRTP
 *  Warning: No virtual destructor; do *not* delete by base class pointer; avoid slicing!
 */
template <typename T> struct HasRepr {
    /** Return the repr as a string */
    inline std::string repr() const {
        std::ostringstream o;
        static_cast<const T &>(*this).repr_stream(o);
        return o.str();
    }

  protected:
    /** Prevent most slicing */
    inline ~HasRepr() noexcept = default;
};

#endif
