/**
 * @file
 * @brief This file defines a method to create an Expression with an literal Op
 */
#ifndef __CREATE_LITERAL_HPP__
#define __CREATE_LITERAL_HPP__

#include "constants.hpp"
#include "private/size.hpp"


namespace Create {

    /** Create a Expression with an literal op */
    template <typename T>
    EBasePtr literal(EAnVec &&av, std::string &&data, const Constants::UInt size) {

        // For brevity
        namespace Ex = Expression;
        using namespace Simplification;
        namespace Err = Error::Expression;

        // Type checks
        static_assert(Utils::is_ancestor<Ex::Base, T>,
                      "Create::literal argument types must be a subclass of Expression::Base");
        static_assert(std::is_final_v<T>, "Create::literal's T must be a final type");

        if constexpr (Utils::is_ancestor<Ex::Bits, T>) {
            // Size check
            Utils::affirm<Utils::Error::Unexpected::Size>(
                size >= data.size(), "Create::literal given size smaller than data size");
            // Construct expression
            return Ex::factory<T>(std::forward<EAnVec>(av), false,
                                  Op::factory<Op::Literal>(std::forward<std::string>(data)), size);
        }
        else {
            // Construct expression
            return Ex::factory<T>(std::forward<EAnVec>(av), false,
                                  Op::factory<Op::Literal>(std::forward<std::string>(data)));
        }
    }

} // namespace Create

#endif
