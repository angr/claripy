/**
 * @file
 * @brief This file defines a method to create Exprs with standard binary ops
 */
#ifndef R_SRC_CREATE_PRIVATE_BINARY_HPP_
#define R_SRC_CREATE_PRIVATE_BINARY_HPP_

#include "size_mode.hpp"

#include "../constants.hpp"


namespace Create::Private {

    /** Calculate the size of a new expression given Mode
     *  Assumes left and right are not null
     *  Assumes left is of type Bits, as is right
     */
    template <SizeMode Mode> U64 binary_len(const Expr::BasePtr &left, const Expr::BasePtr &right) {
        if constexpr (Mode == SizeMode::First) {
            return Expr::bit_length(left);
        }
        else if constexpr (Mode == SizeMode::Add) {
            // Type check before size extraction
            UTIL_ASSERT(Util::Err::Type, left->cuid == right->cuid,
                        "right operand of incorrect type");
            return Expr::bit_length(left) + Expr::bit_length(right);
        }
        else {
            static_assert(Util::CD::false_<Mode>, "Invalid SizeMode");
        }
    }

    /** Create a Expr with a binary op
     *  Expr pointers may not be nullptr
     *  Mode is ignored if left is a Bool
     */
    template <typename Out, typename OpT, SizeMode Mode, typename... Allowed>
    inline Expr::BasePtr binary_explicit(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                         Expr::OpPyDict &&d) {
        static const Expr::TypeNames<Allowed...> allowed;

        // Static checks
        static_assert(Util::Type::Is::ancestor<Expr::Base, Out>,
                      "Create::Private::binary requires Out be an Expr");
        static_assert(Op::is_binary<OpT>, "Create::Private::binary requires a binary OpT");

        // Dynamic checks
        UTIL_ASSERT(Error::Expr::Usage, left && right, "Expr pointer arguments may not be nullptr");
        const bool type_ok { CUID::is_any_t<const Expr::Base, Allowed...>(left) };
        UTIL_ASSERT(Error::Expr::Type, type_ok,
                    "left operand of invalid type; allowed types: ", allowed);

        // Construct expr
        using Simplify::simplify;
        if constexpr (std::is_same_v<Expr::Bool, Out>) {
            return simplify(Expr::factory<Out>(left->symbolic || right->symbolic,
                                               Op::factory<OpT>(left, right), std::move(d)));
        }
        else {
            return simplify(Expr::factory<Out>(left->symbolic || right->symbolic,
                                               Op::factory<OpT>(left, right), std::move(d),
                                               binary_len<Mode>(left, right)));
        }
    }

    /** Create a Expr with a binary op
     *  Out type is the same as left
     *  Expr pointers may not be nullptr
     *  Mode is ignored if left is a Bool
     */
    template <typename OpT, SizeMode Mode, typename... Allowed>
    inline Expr::BasePtr binary(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                Expr::OpPyDict &&d) {
        static_assert(Op::is_binary<OpT>, "Create::Private::binary requires a binary OpT");

        // For speed
        if constexpr (sizeof...(Allowed) == 1) {
            return binary_explicit<Allowed..., OpT, Mode, Allowed...>(left, right, std::move(d));
        }

        // Dynamic checks
        UTIL_ASSERT(Error::Expr::Usage, left && right, "Expr pointer arguments may not be nullptr");
        const bool type_ok { CUID::is_any_t<const Expr::Base, Allowed...>(left) };
        UTIL_ASSERT(Error::Expr::Type, type_ok, "left operand of incorrect type");

        // Create Expr
        using Simplify::simplify;
        if constexpr (Util::Type::Is::in<Expr::Bool, Allowed...>) {
            if (CUID::is_t<Expr::Bool>(left)) {
                return simplify(Expr::factory<Expr::Bool>(left->symbolic || right->symbolic,
                                                          Op::factory<OpT>(left, right),
                                                          std::move(d)));
            }
        }
        return simplify(Expr::factory_cuid(left->cuid, left->symbolic || right->symbolic,
                                           Op::factory<OpT>(left, right), std::move(d),
                                           binary_len<Mode>(left, right)));
    }

} // namespace Create::Private

#endif
