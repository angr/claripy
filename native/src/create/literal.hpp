/**
 * @file
 * @brief This file defines a method to create an Expression with an literal Op
 */
#ifndef __CREATE_LITERAL_HPP__
#define __CREATE_LITERAL_HPP__

#include "constants.hpp"


namespace Create {

    /** Create a Expression with an literal op
     *  A specialization for non-sized classes
     */
    template <typename T> EBasePtr literal(EAnVec &&av, std::string &&data) {

        // For brevity
        namespace Ex = Expression;
        using namespace Simplification;
        namespace Err = Error::Expression;

        // Type checks
        static_assert(Utils::is_ancestor<Ex::Base, T>,
                      "argument types must be a subclass of Expression::Base");
        static_assert(not Utils::is_ancestor<Ex::Bits, T>,
                      "bits subclasses must be passed a bit_length as another argument.");
        static_assert(std::is_final_v<T>, "Create::literal's T must be a final type");

        // Construct expression
        return Ex::factory<T>(std::forward<EAnVec>(av), false,
                              Op::factory<Op::Literal>(std::forward<std::string>(data)));
    }

    /** Create a Expression with an literal op
     *  A specialization for sized classes
     */
    template <typename T>
    EBasePtr literal(EAnVec &&av, std::string &&data, const Constants::UInt bit_length) {

        // For brevity
        namespace Ex = Expression;
        using namespace Simplification;
        namespace Err = Error::Expression;

        // Type checks
        static_assert(Utils::is_ancestor<Ex::Base, T>,
                      "argument types must be a subclass of Expression::Base");
        static_assert(Utils::is_ancestor<Ex::Bits, T>,
                      "non-bits subclasses should not be passed a bit_length argument.");
        static_assert(std::is_final_v<T>, "Create::literal's T must be a final type");

        // Size check
        Utils::affirm<Error::Expression::Size>(bit_length >= (BitLength::char_bit * data.size()),
                                               WHOAMI_WITH_SOURCE
                                               "given size smaller than data size");
        // Construct expression
        return Ex::factory<T>(std::forward<EAnVec>(av), false,
                              Op::factory<Op::Literal>(std::forward<std::string>(data)),
                              bit_length);
    }

} // namespace Create

#endif
