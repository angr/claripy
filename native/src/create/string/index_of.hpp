/**
 * @file
 * @brief This file defines a creation method for an expr containing String::IndexOf
 */
#ifndef R_CREATE_STRING_INDEXOF_HPP_
#define R_CREATE_STRING_INDEXOF_HPP_

#include "../constants.hpp"


namespace Create::String {

    /** Create an Expr with a String::IndexOf op
     *  Expr pointers may not be nullptr
     */
    inline EBasePtr index_of(const EBasePtr &str, const EBasePtr &pattern,
                             const EBasePtr &start_index, const UInt bit_length,
                             Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        Util::affirm<Error::Expr::Usage>(str != nullptr && pattern != nullptr &&
                                             start_index != nullptr,
                                         WHOAMI_WITH_SOURCE "Exprs pointers cannot be nullptr");
        return Simplification::simplify(
            Ex::factory<Ex::BV>(str->symbolic || pattern->symbolic,
                                Op::factory<Op::String::IndexOf>(str, pattern, start_index),
                                bit_length, std::move(sp)));
    }

} // namespace Create::String

#endif
