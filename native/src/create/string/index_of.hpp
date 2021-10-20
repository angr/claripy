/**
 * @file
 * @brief This file defines a creation method for an expression containing String::IndexOf
 */
#ifndef R_CREATE_STRING_INDEXOF_HPP_
#define R_CREATE_STRING_INDEXOF_HPP_

#include "../constants.hpp"


namespace Create::String {

    /** Create an Expression with a String::IndexOf op
     *  Expression pointers may not be nullptr
     */
    inline EBasePtr index_of(const EBasePtr &str, const EBasePtr &pattern,
                             const EBasePtr &start_index, const Constants::UInt bit_length,
                             Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expression;
        Utils::affirm<Error::Expression::Usage>(
            str != nullptr && pattern != nullptr && start_index != nullptr,
            WHOAMI_WITH_SOURCE "Expressions pointers cannot be nullptr");
        return Simplification::simplify(
            Ex::factory<Ex::BV>(str->symbolic || pattern->symbolic,
                                Op::factory<Op::String::IndexOf>(str, pattern, start_index),
                                bit_length, std::move(sp)));
    }

} // namespace Create::String

#endif
