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
                                 const Expr::BasePtr &replacement, Expr::OpPyDict d = {}) {
        UTIL_ASSERT(Error::Expr::Usage, full && search && replacement,
                    "Expr pointers cannot be nullptr");
        UTIL_ASSERT(Error::Expr::Type,
                    CUID::is_t<Expr::String>(full) && CUID::is_t<Expr::String>(search) &&
                        CUID::is_t<Expr::String>(replacement),
                    "operands must be each be of type Expr::String");

        // Construct size
        U64 new_len { Expr::bit_length(full) };
        const auto search_len { Expr::bit_length(search) };
        UTIL_ASSERT(Error::Expr::Size, new_len >= search_len,
                    "The pattern that has to be replaced is longer than the string itself");
        const auto repl_len { Expr::bit_length(replacement) };
        if (search_len < repl_len) {
            new_len += repl_len - search_len;
        }

        // Construct expr
        return Simplify::simplify(Expr::factory<Expr::String>(
            full->symbolic || search->symbolic || replacement->symbolic,
            Op::factory<Op::String::Replace>(full, search, replacement), std::move(d), new_len));
    }

} // namespace Create::String

#endif
