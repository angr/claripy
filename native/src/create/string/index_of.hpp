/**
 * @file
 * @brief This file defines a creation method for an expression containing String::IndexOf
 */
#ifndef __CREATE_STRING_INDEXOF_HPP__
#define __CREATE_STRING_INDEXOF_HPP__

#include "../constants.hpp"
#include "../private/size.hpp"


namespace Create::String {

    /** Create an Expression with a String::IndexOf op */
    inline EBasePtr index_of(EAnVec &&av, const Expression::BasePtr &str,
                             const Expression::BasePtr &pattern, const Constants::UInt start_index,
                             const Constants::UInt bit_length) {
        namespace Ex = Expression;
        return Simplification::simplify(Ex::factory<Ex::BV>(
            std::forward<EAnVec>(av), str->symbolic || pattern->symbolic,
            Op::factory<Op::String::IndexOf>(str, pattern, start_index), bit_length));
    }

} // namespace Create::String

#endif
