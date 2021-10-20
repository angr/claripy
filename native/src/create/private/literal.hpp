/**
 * @file
 * @brief This file defines a method to create an Expr with an literal Op
 */
#ifndef R_CREATE_PRIVATE_LITERAL_HPP_
#define R_CREATE_PRIVATE_LITERAL_HPP_

#include "../constants.hpp"


namespace Create::Private {

    /** Create a Expr with a Literal op
     *  data may not be nullptr
     */
    template <typename T, typename Data> EBasePtr literal(Data &&data, Annotation::SPAV &&sp) {
        namespace Ex = Expr;
        static_assert(Util::is_ancestor<Ex::Base, T>,
                      "argument types must be a subclass of Expr::Base");
        static_assert(std::is_final_v<T>, "Create::literal's T must be a final type");

        // Construct op
        auto op { Op::factory<Op::Literal>(std::move(data)) };

        // Construct expr
        if constexpr (Util::is_ancestor<Ex::Bits, T>) {
            using To = CTSC<Op::Literal>;
            const auto bl { Util::checked_static_cast<To>(op.get())->bit_length() };
            return Ex::factory<T>(false, std::move(op), bl, std::move(sp));
        }
        else {
            return Ex::factory<T>(false, std::move(op), std::move(sp));
        }
    }

} // namespace Create::Private

#endif
