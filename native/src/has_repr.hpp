/**
 * @file
 * @brief This file defines a class that has a repr function
 */
#ifndef R_HASREPR_HPP_
#define R_HASREPR_HPP_

#include "macros.hpp"

#include <sstream>

/** A struct with a repr function */
struct HasRepr {
    /** Virtual destructor */
    virtual inline ~HasRepr() noexcept = default;
    // Rule of 5
    SET_IMPLICITS(HasRepr, default, noexcept);

    /** Add the repr to the stream */
    virtual void repr_stream(std::ostream &) const = 0;

    /** Return the repr as a string */
    inline std::string repr() const {
        std::ostringstream o;
        repr_stream(o);
        return o.str();
    }
};

#endif
