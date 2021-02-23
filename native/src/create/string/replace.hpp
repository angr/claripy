/**
 * @file
 * @brief This file defines a creation method for an expression containing String::Replace
 */
#ifndef __CREATE_STRING_REPLACE_HPP__
#define __CREATE_STRING_REPLACE_HPP__

#include "../constants.hpp"
#include "../private/bit_length.hpp"


namespace Create::String {

    /** Create an Expression with a String::Replace op */
    inline EBasePtr replace(EAnVec &&av, const EBasePtr &first, const EBasePtr &second,
                            const EBasePtr &third) {

        // For brevity
        namespace Ex = Expression;
        using namespace Simplification;
        namespace CP = ::Create::Private;
        namespace Err = Error::Expression;

        // Type check
        Utils::affirm<Err::Type>(CUID::is_t<Ex::String>(first) && CUID::is_t<Ex::String>(second) &&
                                     CUID::is_t<Ex::String>(third),
                                 WHOAMI_WITH_SOURCE
                                 "operands must be each be of type Expression::String");

        // Construct size
        Constants::UInt new_bit_length { CP::bit_length(first) };
        const auto s2 { CP::bit_length(second) };
        Utils::affirm<Err::Size>(
            new_bit_length >= s2, WHOAMI_WITH_SOURCE
            "The pattern that has to be replaced is longer than the string itself");
        const auto s3 { CP::bit_length(third) };
        if (s2 < s3) {
            new_bit_length = new_bit_length - s2 + s3;
        }

        // Construct expression
        return simplify(Ex::factory<Ex::String>(
            std::forward<EAnVec>(av), first->symbolic || second->symbolic || third->symbolic,
            Op::factory<Op::String::Replace>(first, second, third), new_bit_length));
    }

} // namespace Create::String

#endif
