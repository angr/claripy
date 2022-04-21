/**
 * @file
 * @brief This file defines a creation method for an expr containing String::SubString
 */
#ifndef R_SRC_CREATE_STRING_SUBSTRING_HPP_
#define R_SRC_CREATE_STRING_SUBSTRING_HPP_

#include "../constants.hpp"


namespace Create::String {

    namespace Private {
        /** Calculate the length for a SubString expr
         *  Expr pointers may not be nullptr
         *  @todo Adjust as we edit concrete
         */
        static inline U64 sub_string_length(const Expr::BasePtr &count,
                                            const Expr::BasePtr &full_string) {
            using E = Error::Expr::Type;
            // If symbolic, use full_string's length
            if (count->symbolic) {
                UTIL_ASSERT(E, CUID::is_t<Expr::String>(full_string),
                            "full_string expr must be a String");
                return Expr::get_bit_length(full_string);
            }
            // If concrete, use Concrete Op's length
            else {
#ifdef DEBUG
                UTIL_ASSERT(E, CUID::is_t<Expr::BV>(count), "count expr must be a BV");
#endif
                UTIL_ASSERT(E, CUID::is_t<Op::Literal>(count->op),
                            "count op must be a Literal. More than likely, this means that some "
                            "simplifiers are unimplemented / failing.");
                return 0x1000; // NOLINT TODO
            }
        }
    } // namespace Private

    /** Create an Expr with a String::SubString op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr sub_string(const Expr::BasePtr &start_index, const Expr::BasePtr &count,
                                    const Expr::BasePtr &full_string,
                                    Annotation::SPAV sp = empty_spav) {
        UTIL_ASSERT(Error::Expr::Usage, start_index && count && full_string,
                    "Expr pointers cannot be nullptr");
        const U64 bit_length { Private::sub_string_length(count, full_string) };
        return Simplify::simplify(Expr::factory<Expr::String>(
            start_index->symbolic || count->symbolic || full_string->symbolic,
            Op::factory<Op::String::SubString>(start_index, count, full_string), bit_length,
            std::move(sp)));
    }

} // namespace Create::String

#endif
