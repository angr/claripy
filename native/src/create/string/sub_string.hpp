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
         */
        static inline U64 sub_string_length(const Expr::BasePtr &count,
                                            const Expr::BasePtr &full_string) {
            UTIL_ASSERT(Error::Expr::Type, CUID::is_t<Expr::String>(full_string),
                        "full_string expr must be a String");
            UTIL_ASSERT_NOT_NULL_DEBUG(count);
            if (CUID::is_t<Op::Literal>(count->op) && CUID::is_t<Expr::BV>(count)) {
                UTIL_ASSERT_NOT_NULL_DEBUG(count->op);
                const auto &prim {
                    Util::checked_static_cast<CTSC<Op::Literal>>(count->op.get())->value
                };
                switch (prim.index()) {
#define M_GET(TYPE)                                                                                \
    case Util::Type::index<decltype(prim), TYPE>:                                                  \
        return CHAR_BIT * static_cast<U64>(std::get<TYPE>(prim))
                    M_GET(uint8_t);
                    M_GET(uint16_t);
                    M_GET(uint32_t);
                    M_GET(U64);
#undef M_GET
                }
            }
            return Expr::bit_length(full_string);
        }
    } // namespace Private

    /** Create an Expr with a String::SubString op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr sub_string(const Expr::BasePtr &start_index, const Expr::BasePtr &count,
                                    const Expr::BasePtr &full_string, Expr::OpPyDict d = {}) {
        UTIL_ASSERT(Error::Expr::Usage, start_index && count && full_string,
                    "Expr pointers cannot be nullptr");
        const U64 bit_length { Private::sub_string_length(count, full_string) };
        return Simplify::simplify(Expr::factory<Expr::String>(
            start_index->symbolic || count->symbolic || full_string->symbolic,
            Op::factory<Op::String::SubString>(start_index, count, full_string), std::move(d),
            bit_length));
    }

} // namespace Create::String

#endif
