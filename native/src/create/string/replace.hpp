/**
 * @file
 * @brief This file defines a creation method for an expression containing String::Replace
 */
#ifndef __CREATE_STRING_REPLACE_HPP__
#define __CREATE_STRING_REPLACE_HPP__

#include "../constants.hpp"
#include "../private/size.hpp"


namespace Create::String {

    /** Create an Expression with a String::Replace op */
    inline EBasePtr replace(EAnVec &&av, const EBasePtr &first, const EBasePtr &second,
                            const EBasePtr &third) {

        // For brevity
        namespace Ex = Expression;
        using namespace Simplification;
        namespace Err = Error::Expression;

        // Type check
        Utils::affirm<Err::Type>(
            Ex::is_t<Ex::String>(first) && Ex::is_t<Ex::String>(second) &&
                Ex::is_t<Ex::String>(third),
            "Create::String::replace operands must be each be of type Expression::String");

        // Construct size
        Constants::UInt esize { Private::size(first) };
        const auto s2 { Private::size(second) };
        Utils::affirm<Err::Size>(
            esize >= s2, "The pattern that has to be replaced is longer than the string itself");
        const auto s3 { Private::size(third) };
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
