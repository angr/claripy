/**
 * @file
 * @brief This file defines a creation method for an expr containing String::SubString
 */
#ifndef R_CREATE_STRING_SUBSTRING_HPP_
#define R_CREATE_STRING_SUBSTRING_HPP_

#include "../constants.hpp"


namespace Create::String {

    namespace Private {
        /** Calculate the length for a SubString expr
         *  Expr pointers may not be nullptr
         *  @todo Adjust as we edit concrete
         */
        static inline UInt sub_string_length(const EBasePtr &count, const EBasePtr &full_string) {
            using Err = Error::Expr::Type;
            // If symbolic, use full_string's length
            if (count->symbolic) {
                Util::affirm<Err>(CUID::is_t<Expr::String>(full_string),
                                  WHOAMI_WITH_SOURCE "full_string expr must be a String");
                return Expr::get_bit_length(full_string);
            }
            // If concrete, use Concrete Op's length
            else {
#ifdef DEBUG
                Util::affirm<Err>(CUID::is_t<Expr::BV>(count),
                                  WHOAMI_WITH_SOURCE "count expr must be a BV");
#endif
                Util::affirm<Err>(CUID::is_t<Op::Literal>(count->op), WHOAMI_WITH_SOURCE
                                  "count op must be a Literal. More than likely, this means "
                                  "that some simplifiers are unimplemented / failing.");
                return 0x1000; // NOLINT TODO
            }
        }
    } // namespace Private

    /** Create an Expr with a String::SubString op
     *  Expr pointers may not be nullptr
     */
    inline EBasePtr sub_string(const EBasePtr &start_index, const EBasePtr &count,
                               const EBasePtr &full_string, Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        Util::affirm<Error::Expr::Usage>(start_index != nullptr && count != nullptr &&
                                             full_string != nullptr,
                                         WHOAMI_WITH_SOURCE "Expr pointers cannot be nullptr");
        const UInt bit_length { Private::sub_string_length(count, full_string) };
        return Simplification::simplify(Ex::factory<Ex::String>(
            start_index->symbolic || count->symbolic || full_string->symbolic,
            Op::factory<Op::String::SubString>(start_index, count, full_string), bit_length,
            std::move(sp)));
    }

} // namespace Create::String

#endif
