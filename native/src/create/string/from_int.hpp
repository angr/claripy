/**
 * @file
 * @brief This file defines a creation method for an expr containing String::FromInt
 */
#ifndef R_SRC_CREATE_STRING_FROMINT_HPP_
#define R_SRC_CREATE_STRING_FROMINT_HPP_

#include "../constants.hpp"


namespace Create::String {

    /** Create an Expr with a String::FromInt op
     *  Note: Currently Ints are taken in as BVs
     *  Note: For now, we just set the size to 2 bytes larger than the input
     *  This should be large-enough, and isn't as bad an over-estimation as INT_MAX or anything
     *  Expr pointers may not be nullptr
     *  Note: This is not trivial due to its length calculation
     *  TODO: length might want to be: Expr::bit_length(x) + 2_ui * CHAR_BIT
     */
    inline Expr::BasePtr from_int(const Expr::BasePtr &x, Expr::OpPyDict d = {}) {
        UTIL_ASSERT(Error::Expr::Usage, x, "Expr pointers cannot be nullptr");
        UTIL_ASSERT(Error::Expr::Type, CUID::is_t<Expr::BV>(x),
                    "operand must be each be of type Expr::BV");
        return Simplify::simplify(Expr::factory<Expr::String>(
            x->symbolic, Op::factory<Op::String::FromInt>(x), std::move(d), CHAR_BIT * 10000_ui));
    }

} // namespace Create::String

#endif
