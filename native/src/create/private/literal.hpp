/**
 * @file
 * @brief This file defines a method to create an Expression with an literal Op
 */
#ifndef __CREATE_PRIVATE_LITERAL_HPP__
#define __CREATE_PRIVATE_LITERAL_HPP__

#include "../constants.hpp"


namespace Create::Private {

    /** Create a Expression with a Literal op */
    template <typename T, typename Data> EBasePtr literal(EAnVec &&av, Data &&data) {
        namespace Ex = Expression;

        // Type checks
        static_assert(Utils::is_ancestor<Ex::Base, T>,
                      "argument types must be a subclass of Expression::Base");
        static_assert(std::is_final_v<T>, "Create::literal's T must be a final type");

        // Construct op
        auto op { Op::factory<Op::Literal>(std::move(data)) };

        // Construct expression
        if constexpr (Utils::is_ancestor<Ex::Bits, T>) {
            using To = Constants::CTSC<Op::Literal>;
            const auto bl { Utils::checked_static_cast<To>(op.get())->bit_length() };
            return Ex::factory<T>(std::forward<EAnVec>(av), false, std::move(op), bl);
        }
        else {
            return Ex::factory<T>(std::forward<EAnVec>(av), false, std::move(op));
        }
    }

} // namespace Create::Private

#endif
