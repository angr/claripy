/**
 * @file
 * @brief This file defines a creation method for an expression containing String::IndexOf
 */
#ifndef R_CREATE_STRING_INDEXOF_HPP_
#define R_CREATE_STRING_INDEXOF_HPP_

#include "../constants.hpp"


namespace Create::String {

    /** Create an Expression with a String::IndexOf op */
    inline EBasePtr index_of(EAnVec &&av, const Expression::BasePtr &str,
                             const Expression::BasePtr &pattern,
                             const Expression::BasePtr &start_index,
                             const Constants::UInt bit_length) {
        namespace Ex = Expression;
        return Simplification::simplify(Ex::factory<Ex::BV>(
            std::forward<EAnVec>(av), str->symbolic || pattern->symbolic,
            Op::factory<Op::String::IndexOf>(str, pattern, start_index), bit_length));
    }

} // namespace Create::String

#endif
