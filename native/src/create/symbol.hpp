/**
 * @file
 * @brief This file defines a method to create an Expression with an symbol Op
 */
#ifndef __CREATE_SYMBOL_HPP__
#define __CREATE_SYMBOL_HPP__

#include "constants.hpp"


namespace Create {

    /** Create a Expression with an symbol op
     *  This override is for non-sized symbols
     */
    template <typename T> EBasePtr symbol(EAnVec &&av, std::string &&name) {
        namespace Ex = Expression;

        // Type checks
        static_assert(Utils::is_ancestor<Ex::Base, T>,
                      "Create::symbol argument types must be a subclass of Expression::Base");
        static_assert(!Utils::is_ancestor<Ex::Bits, T>,
                      "Incorrect Create::symbol funciton called for T. Bits subclasses"
                      " require a size argument after the name argument");
        static_assert(std::is_final_v<T>, "Create::symbol's T must be a final type");

        // Construct expression
        return Ex::factory<T>(std::forward<EAnVec>(av), true,
                              Op::factory<Op::Symbol>(std::forward<std::string>(name)));
    }

    /** Create a Expression with an symbol op
     *  This override is for sized symbols
     */
    template <typename T>
    EBasePtr symbol(EAnVec &&av, std::string &&name, const Constants::UInt bit_length) {
        namespace Ex = Expression;

        // Type checks
        static_assert(Utils::is_ancestor<Ex::Bits, T>,
                      "Create::symbol argument types must be a subclass of Bits");
        static_assert(std::is_final_v<T>, "Create::symbol's T must be a final type");

        // Construct expression
        return Ex::factory<T>(std::forward<EAnVec>(av), true,
                              Op::factory<Op::Symbol>(std::forward<std::string>(name)),
                              bit_length);
    }

} // namespace Create

#endif
