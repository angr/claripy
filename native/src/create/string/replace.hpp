/**
 * @file
 * @brief This file defines a creation method for an expr containing String::Replace
 */
#ifndef R_SRC_CREATE_STRING_REPLACE_HPP_
#define R_SRC_CREATE_STRING_REPLACE_HPP_

#include "../constants.hpp"


namespace Create::String {

    /** Create an Expr with a String::Replace op
     *  Despite being ternary, this is not a trivial op because of the unique length calculation
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr replace(const Expr::BasePtr &full, const Expr::BasePtr &search,
                                 const Expr::BasePtr &replacement,
                                 Annotation::SPAV sp = empty_spav) {
        using namespace Simplify;
        namespace Err = Error::Expr;

        // Checks
        UTIL_ASSERT(Err::Usage, full != nullptr && search != nullptr && replacement != nullptr,
                    "Expr pointers cannot be nullptr");
        UTIL_ASSERT(Err::Type,
                    CUID::is_t<Expr::String>(full) && CUID::is_t<Expr::String>(search) &&
                        CUID::is_t<Expr::String>(replacement),
                    "operands must be each be of type Expr::String");

        // Construct size
        U64 new_bit_length { Expr::get_bit_length(full) };
        const auto s2 { Expr::get_bit_length(search) };
        UTIL_ASSERT(Err::Size, new_bit_length >= s2,
                    "The pattern that has to be replaced is longer than the string itself");
        const auto s3 { Expr::get_bit_length(replacement) };
        if (s2 < s3) {
            new_bit_length += s3 - s2;
        }

        // Construct expr
        return simplify(
            Expr::factory<Expr::String>(full->symbolic || search->symbolic || replacement->symbolic,
                                        Op::factory<Op::String::Replace>(full, search, replacement),
                                        new_bit_length, std::move(sp)));
    }

} // namespace Create::String

#endif
