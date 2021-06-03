/**
 * @file
 * @brief This file defines a creation method for an expression containing String::SubString
 */
#ifndef R_CREATE_STRING_SUBSTRING_HPP_
#define R_CREATE_STRING_SUBSTRING_HPP_

#include "../constants.hpp"


namespace Create::String {

    namespace Private {
        /** Calculate the length for a SubString expression
         *  Expression pointers may not be nullptr
         *  @todo Adjust as we edit concrete
         */
        static inline Constants::UInt sub_string_length(const EBasePtr &count,
                                                        const EBasePtr &full_string) {
            using Err = Error::Expression::Type;
            // If symbolic, use full_string's length
            if (count->symbolic) {
                Utils::affirm<Err>(CUID::is_t<Expression::String>(full_string),
                                   WHOAMI_WITH_SOURCE "full_string expression must be a String");
                return Expression::get_bit_length(full_string);
            }
            // If concrete, use Concrete Op's length
            else {
#ifdef DEBUG
                Utils::affirm<Err>(CUID::is_t<Expression::BV>(count),
                                   WHOAMI_WITH_SOURCE "count expression must be a BV");
#endif
                Utils::affirm<Err>(CUID::is_t<Op::Literal>(count->op), WHOAMI_WITH_SOURCE
                                   "count op must be a Literal. More than likely, this means "
                                   "that some simplifiers are unimplemented / failing.");
                return 0x1000; // NOLINT TODO
            }
        }
    } // namespace Private

    /** Create an Expression with a String::SubString op
     *  Expression pointers may not be nullptr
     */
    inline EBasePtr sub_string(const EBasePtr &start_index, const EBasePtr &count,
                               const EBasePtr &full_string, SPAV &&sp = nullptr) {
        namespace Ex = Expression;
        Utils::affirm<Error::Expression::Usage>(
            start_index != nullptr && count != nullptr && full_string != nullptr,
            WHOAMI_WITH_SOURCE "Expression pointers cannot be nullptr");
        const Constants::UInt bit_length { Private::sub_string_length(count, full_string) };
        return Simplification::simplify(Ex::factory<Ex::String>(
            start_index->symbolic || count->symbolic || full_string->symbolic,
            Op::factory<Op::String::SubString>(start_index, count, full_string), bit_length,
            std::move(sp)));
    }

} // namespace Create::String

#endif
