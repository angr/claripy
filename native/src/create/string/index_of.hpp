/**
 * @file
 * @brief This file defines a creation method for an expression containing String::IndexOf
 */
#ifndef R_CREATE_STRING_INDEXOF_HPP_
#define R_CREATE_STRING_INDEXOF_HPP_

#include "../constants.hpp"


namespace Create::String {

    /** Create an Expression with a String::IndexOf op */
    inline EBasePtr index_of(const Expression::BasePtr &str, const Expression::BasePtr &pattern,
                             const Expression::BasePtr &start_index,
                             const Constants::UInt bit_length, SPAV &&sp = nullptr) {
        namespace Ex = Expression;
        return Simplification::simplify(
            Ex::factory<Ex::BV>(str->symbolic || pattern->symbolic,
                                Op::factory<Op::String::IndexOf>(str, pattern, start_index),
                                bit_length, std::move(sp)));
    }

} // namespace Create::String

#endif
