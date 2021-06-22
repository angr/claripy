/**
 * @file
 * @brief This file defines the repr function for expressions
 * Note that these are not member functions because they require knowledge of op internals
 */
#ifndef R_EXPRESSION_REPR_HPP_
#define R_EXPRESSION_REPR_HPP_

#include "base.hpp"

#include <sstream>


namespace Expression {

    /** The repr function for expressions (outputs json)
     *  e may not be nullptr
     */
    void repr(const RawPtr e, std::ostream &out, const bool verbose = false);

    /** The repr function for expressions (outputs json)
     *  e may not be nullptr
     */
    inline void repr(const BasePtr &e, std::ostream &out, const bool verbose = false) {
        repr(e.get(), out, verbose);
    }

    /** repr, but returns the result as a string
     *  e may not be nullptr
     */
    inline std::string inline_repr(const RawPtr e, const bool verbose = false) {
        std::ostringstream o;
        repr(e, o, verbose);
        return o.str();
    }

    /** repr, but returns the result as a string
     *  e may not be nullptr
     */
    inline std::string inline_repr(const BasePtr &e, const bool verbose = false) {
        std::ostringstream o;
        repr(e, o, verbose);
        return o.str();
    }

    /** Overload the << stream operator to use repr */
    inline std::ostream &operator<<(std::ostream &os, const BasePtr &p) {
        repr(p, os, false);
        return os;
    }

    /** Overload the << stream operator to use repr */
    inline std::ostream &operator<<(std::ostream &os, const RawPtr &p) {
        repr(p, os, false);
        return os;
    }

} // namespace Expression

#endif
