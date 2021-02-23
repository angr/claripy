/**
 * @file
 * @brief This file defines a creation method for an expression containing String::SubString
 */
#ifndef __CREATE_STRING_SUBSTRING_HPP__
#define __CREATE_STRING_SUBSTRING_HPP__

#include "../constants.hpp"
#include "../private/bit_length.hpp"


namespace Create::String {

    namespace Private {
        /** Calculate the length for a SubString expression
         *  @todo Adjust as we edit concrete
         */
        static inline Constants::UInt sub_string_length(const Expression::BasePtr &count,
                                                        const Expression::BasePtr &full_string) {

            // For brevity
            using Err = Error::Expression::Type;
            namespace CP = ::Create::Private;

            // If symbolic, use full_string's length
            if (count->symbolic) {
                Utils::affirm<Err>(CUID::is_t<Expression::String>(full_string),
                                   WHOAMI_WITH_SOURCE "full_string expression must be a String");
                return CP::bit_length(full_string);
            }

            // If concrete, use Concrete Op's length
            else {
#ifdef DEBUG
                Utils::affirm<Err>(CUID::is_t<Expression::BV>(count),
                                   WHOAMI_WITH_SOURCE "count expression must be a BV");
#endif
                Utils::affirm<Err>(CUID::is_t<Op::Literal>(count->op), WHOAMI_WITH_SOURCE
                                   "count op must be a Concrete. More than likely, this means "
                                   "that some simplifiers are unimplemented / failing.");
                return 0x1000; // NOLINT TODO
            }
        }
    } // namespace Private

    /** Create an Expression with a String::SubString op */
    inline EBasePtr index_of(EAnVec &&av, const Expression::BasePtr &start_index,
                             const Expression::BasePtr &count,
                             const Expression::BasePtr &full_string) {
        namespace Ex = Expression;
        const Constants::UInt bit_length { Private::sub_string_length(count, full_string) };
        return Simplification::simplify(Ex::factory<Ex::String>(
            std::forward<EAnVec>(av),
            start_index->symbolic || count->symbolic || full_string->symbolic,
            Op::factory<Op::String::SubString>(start_index, count, full_string), bit_length));
    }

} // namespace Create::String

#endif
