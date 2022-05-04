/**
 * @file
 * @brief This file defines a method to create an Expr with an literal Op
 */
#ifndef R_SRC_CREATE_PRIVATE_LITERAL_HPP_
#define R_SRC_CREATE_PRIVATE_LITERAL_HPP_

#include "../constants.hpp"


namespace Create::Private {

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
        uint8_t, Expr::BV, uint16_t, Expr::BV, uint32_t, Expr::BV, U64, Expr::BV, BigInt, Expr::BV>;

    /** Create a Expr with a Literal op
     *  data may not be nullptr
     */
    template <typename Data> Expr::BasePtr literal(Data &&data, Annotation::SPAV &&sp) {
        using T = TypeMap::template GetValue<std::remove_cv_t<std::remove_reference_t<Data>>>;
        auto op { Op::factory<Op::Literal>(std::move(data)) };
        if constexpr (Util::Type::Is::ancestor<Expr::Bits, T>) {
            UTIL_ASSERT_NOT_NULL_DEBUG(op.get());
            using To = CTSC<Op::Literal>;
            const auto bl { Op::bit_length(Util::checked_static_cast<To>(op.get())->value) };
            return Expr::factory<T>(false, std::move(op), bl, std::move(sp));
        }
        else {
            return Expr::factory<T>(false, std::move(op), std::move(sp));
        }
    }
} // namespace Create::Private

#endif
