/**
 * @file
 * @brief This file defines a creation method for an expression containing String::FromInt
 */
#ifndef __CREATE_STRING_FROMINT_HPP__
#define __CREATE_STRING_FROMINT_HPP__

#include "../constants.hpp"
#include "../private/bit_length.hpp"


namespace Create::String {

    /** Create an Expression with a String::FromInt op
     *  Note: Currently Ints are taken in as BVs
     *  Note: For now, we just set the size to 2 bytes larger than the input
     *  This should be large-enough, and isn't as bad an over-estimation as INT_MAX or anything
     */
    inline EBasePtr from_int(EAnVec &&av, const EBasePtr &x) {
        namespace Ex = Expression;
        Utils::affirm<Error::Expression::Type>(CUID::is_t<Ex::BV>(x), WHOAMI_WITH_SOURCE
                                               "operand must be each be of type Expression::BV");
        return Simplification::simplify(Ex::factory<Ex::String>(
            std::forward<EAnVec>(av), x->symbolic, Op::factory<Op::String::FromInt>(x),
            ::Create::Private::bit_length(x) + 2_ui * BitLength::char_bit));
    }

} // namespace Create::String

#endif
