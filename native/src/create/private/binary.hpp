/**
 * @file
 * @brief This file defines a method to create Expressions with standard binary ops
 */
#ifndef __CREATE_PRIVATE_BINARY_HPP__
#define __CREATE_PRIVATE_BINARY_HPP__

#include "size.hpp"
#include "size_mode.hpp"

#include "../constants.hpp"


namespace Create::Private {

    /** Create a Expression with a binary op */
    template <typename T, typename OpT, SizeMode Mode, typename... Allowed>
    EBasePtr binary(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {

        // For brevity
        namespace Ex = Expression;
        using namespace Simplification;
        namespace Err = Error::Expression;

        // Type check
        static_assert(Utils::qualified_is_in<T, Allowed...>,
                      "Create::Private::binary requires T is in Allowed");
        static_assert(Op::is_binary<OpT>, "Create::Private::binary requries OpT to be binary");
        Utils::affirm<Err::Type>(Ex::is_t<T>(left),
                                 "Create::Private::binary left operands of incorrect type");

        // Construct expression (static casts are safe because of previous checks)
        if constexpr (Utils::is_ancestor<Ex::Bits, T>) {
            // Construct size
            Constants::UInt esize { size(left) };
            if constexpr (Mode == SizeMode::Add) {
                esize += size(right);
            }
            else if constexpr (Mode != SizeMode::First) {
                static_assert(Utils::TD::false_<Mode>,
                              "Create::Private::binary does not support the given SizeMode");
            }
            // Actually construct expression
            return simplify(Ex::factory<T>(std::forward<EAnVec>(av),
                                           left->symbolic || right->symbolic,
                                           Op::factory<OpT>(left, right), esize));
        }
        else {
            static_assert(Mode == Utils::TD::id<SizeMode::NA>,
                          "SizeMode should be NA for non-sized type");
            return simplify(Ex::factory<T>(std::forward<EAnVec>(av),
                                           left->symbolic || right->symbolic,
                                           Op::factory<OpT>(left, right)));
        }
    }

} // namespace Create::Private


#endif
