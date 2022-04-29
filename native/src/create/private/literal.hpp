/**
 * @file
 * @brief This file defines a method to create an Expr with an literal Op
 */
#ifndef R_SRC_CREATE_PRIVATE_LITERAL_HPP_
#define R_SRC_CREATE_PRIVATE_LITERAL_HPP_

#include "../constants.hpp"


namespace Create::Private {

    /** Create a Expr with a Literal op
     *  data may not be nullptr
     */
    template <typename T, typename Data> Expr::BasePtr literal(Data &&data, Annotation::SPAV &&sp) {
        static_assert(Util::Type::Is::ancestor<Expr::Base, T>,
                      "argument types must be a subclass of Expr::Base");
        static_assert(std::is_final_v<T>, "Create::literal's T must be a final type");

        // Construct op
        auto op { Op::factory<Op::Literal>(std::move(data)) };

        // Construct expr
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
