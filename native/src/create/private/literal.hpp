/**
 * @file
 * @brief This file defines a method to create an Expr with an literal Op
 */
#ifndef R_SRC_CREATE_PRIVATE_LITERAL_HPP_
#define R_SRC_CREATE_PRIVATE_LITERAL_HPP_

#include "../constants.hpp"


namespace Create::Private {

    /** Create a Expr with a Literal op
     *  data may not be OpPyDict{}
     */
    inline Expr::BasePtr literal(std::string &&data, Expr::OpPyDict &&d, const U64 bit_length) {
        auto op { Op::factory<Op::Literal>(std::move(data)) };
        UTIL_ASSERT_NOT_NULL_DEBUG(op.get());
        return Expr::factory<Expr::String>(false, std::move(op), std::move(d), bit_length);
    }

    /** Create a Expr with a Literal op
     *  data may not be nullptr
     */
    template <typename Data> Expr::BasePtr literal(Data &&data, Expr::OpPyDict &&d) {
        // Determine expr type
        using TypeMap = Util::Type::Map<
            // Bool
            bool, Expr::Bool,
            // String
            std::string, Expr::String,
            // VS
            PyObj::VS::Ptr, Expr::VS,
            // FP
            double, Expr::FP, float, Expr::FP,
            // BV
            uint8_t, Expr::BV, uint16_t, Expr::BV, uint32_t, Expr::BV, U64, Expr::BV, BigInt,
            Expr::BV>;
        using ExprT = TypeMap::template GetValue<Util::Type::RemoveCVR<Data>>;
        // Construct expr
        auto op { Op::factory<Op::Literal>(std::move(data)) };
        if constexpr (not Util::Type::Is::ancestor<Expr::Bits, ExprT>) {
            return Expr::factory<ExprT>(false, std::move(op), std::move(d));
        }
        else {
            using To = CTSC<Op::Literal>;
            UTIL_ASSERT_NOT_NULL_DEBUG(op.get());
            const auto bl { Op::bit_length(Util::checked_static_cast<To>(op.get())->value) };
            return Expr::factory<ExprT>(false, std::move(op), std::move(d), bl);
        }
    }

} // namespace Create::Private

#endif
