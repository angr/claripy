/**
 * @file
 * @brief This file defines a creation method for an expression containing String::FromInt
 */
#ifndef R_CREATE_STRING_FROMINT_HPP_
#define R_CREATE_STRING_FROMINT_HPP_

#include "../constants.hpp"


namespace Create::String {

    /** Create an Expression with a String::FromInt op
     *  Note: Currently Ints are taken in as BVs
     *  Note: For now, we just set the size to 2 bytes larger than the input
     *  This should be large-enough, and isn't as bad an over-estimation as INT_MAX or anything
     *  Expression pointers may not be nullptr
     */
    inline EBasePtr from_int(const EBasePtr &x, SPAV &&sp = nullptr) {
        namespace Ex = Expression;
        namespace Err = Error::Expression;
        Utils::affirm<Err::Usage>(x != nullptr,
                                  WHOAMI_WITH_SOURCE "Expression pointers cannot be nullptr");
        Utils::affirm<Err::Type>(CUID::is_t<Ex::BV>(x), WHOAMI_WITH_SOURCE
                                 "operand must be each be of type Expression::BV");
        return Simplification::simplify(Ex::factory<Ex::String>(
            x->symbolic, Op::factory<Op::String::FromInt>(x),
            Ex::get_bit_length(x) + 2_ui * BitLength::char_bit, std::move(sp)));
    }

} // namespace Create::String

#endif
