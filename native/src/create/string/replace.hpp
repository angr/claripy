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
        namespace Err = Error::Expression;

        // Type check
        Utils::affirm<Err::Type>(Ex::is_t<Ex::String>(first) && Ex::is_t<Ex::String>(second) &&
                                     Ex::is_t<Ex::String>(third),
                                 WHOAMI_WITH_SOURCE
                                 "operands must be each be of type Expression::String");

        // Construct size
        Constants::UInt esize { Private::bit_length(first) };
        const auto s2 { Private::bit_length(second) };
        Utils::affirm<Err::Size>(
            esize >= s2, WHOAMI_WITH_SOURCE
            "The pattern that has to be replaced is longer than the string itself");
        const auto s3 { Private::bit_length(third) };
        if (s2 < s3) {
            esize = esize - s2 + s3;
        }

        // Construct expression
        return simplify(Ex::factory<Ex::String>(
            std::forward<EAnVec>(av), first->symbolic || second->symbolic || third->symbolic,
            Op::factory<Op::String::Replace>(first, second, third), esize));
    }

} // namespace Create::String

#endif
