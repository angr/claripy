/**
 * @file
 * @brief This file defines a creation method for an expression containing String::Replace
 */
#ifndef R_CREATE_STRING_REPLACE_HPP_
#define R_CREATE_STRING_REPLACE_HPP_

#include "../constants.hpp"


namespace Create::String {

    /** Create an Expression with a String::Replace op
     *  Despite being ternary, this is not a trivial op because of the unique length calculation
     *  Expression pointers may not be nullptr
     */
    inline EBasePtr replace(const EBasePtr &first, const EBasePtr &second, const EBasePtr &third,
                            Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expression;
        using namespace Simplification;
        namespace Err = Error::Expression;

        // Checks
        Utils::affirm<Err::Usage>(first != nullptr && second != nullptr && third != nullptr,
                                  WHOAMI_WITH_SOURCE "Expression pointers cannot be nullptr");
        Utils::affirm<Err::Type>(CUID::is_t<Ex::String>(first) && CUID::is_t<Ex::String>(second) &&
                                     CUID::is_t<Ex::String>(third),
                                 WHOAMI_WITH_SOURCE
                                 "operands must be each be of type Expression::String");

        // Construct size
        UInt new_bit_length { Ex::get_bit_length(first) };
        const auto s2 { Ex::get_bit_length(second) };
        Utils::affirm<Err::Size>(
            new_bit_length >= s2, WHOAMI_WITH_SOURCE
            "The pattern that has to be replaced is longer than the string itself");
        const auto s3 { Ex::get_bit_length(third) };
        if (s2 < s3) {
            new_bit_length += s3 - s2;
        }

        // Construct expression
        return simplify(
            Ex::factory<Ex::String>(first->symbolic || second->symbolic || third->symbolic,
                                    Op::factory<Op::String::Replace>(first, second, third),
                                    new_bit_length, std::move(sp)));
    }

} // namespace Create::String

#endif
