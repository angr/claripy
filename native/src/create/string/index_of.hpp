/**
 * @file
 * @brief This file defines a creation method for an expr containing String::IndexOf
 */
#ifndef R_SRC_CREATE_STRING_INDEXOF_HPP_
#define R_SRC_CREATE_STRING_INDEXOF_HPP_

#include "../constants.hpp"


namespace Create::String {

    /** Create an Expr with a String::IndexOf op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr index_of(const Expr::BasePtr &str, const Expr::BasePtr &pattern,
                                  const Expr::BasePtr &start_index, const U64 bit_length,
                                  Annotation::SPAV sp = empty_spav) {
        UTIL_ASSERT(Error::Expr::Usage,
                    str != nullptr && pattern != nullptr && start_index != nullptr,
                    "Exprs pointers cannot be nullptr");
        return Simplify::simplify(
            Expr::factory<Expr::BV>(str->symbolic || pattern->symbolic,
                                    Op::factory<Op::String::IndexOf>(str, pattern, start_index),
                                    bit_length, std::move(sp)));
    }

} // namespace Create::String

#endif
