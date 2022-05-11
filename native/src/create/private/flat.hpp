/**
 * @file
 * @brief This file defines a method to create Exprs with standard flat ops
 */
#ifndef R_SRC_CREATE_PRIVATE_FLAT_HPP_
#define R_SRC_CREATE_PRIVATE_FLAT_HPP_

#include "../constants.hpp"


namespace Create::Private {

    /** Ors the sym value of each Expr::BasePtr item in C */
    template <typename C> inline bool flat_sym(C &&o) {
        bool sym { false };
        for (const Expr::BasePtr &i : o) {
#ifdef DEBUG
            UTIL_ASSERT(Error::Expr::Usage, i, "Null operand detected");
#endif
            sym |= i->symbolic;
        }
        return sym;
    }

    /** Create a Expr with a flat op
     *  operands' pointers may not be nullptr
     *  SizeMode is assumed to be First
     */
    template <typename Out, typename OpT, typename... Allowed>
    inline Expr::BasePtr flat_explicit(Op::FlatArgs &&operands, Annotation::SPAV &&sp) {
        static const Expr::TypeNames<Allowed...> allowed;
        using namespace Simplify;
        namespace Err = Error::Expr;

        // Checks
        static_assert(Op::is_flat<OpT>, "Create::Private::flat requires OpT to be flat");
        static_assert(Util::Type::Is::in<Out, Allowed...>,
                      "Create::Private::flat argument types must be in Allowed");
        UTIL_ASSERT(Err::Size, operands.size() >= 2, "operands are empty.");
        UTIL_ASSERT_NOT_NULL_DEBUG(operands[0]);
        UTIL_ASSERT(Err::Type, CUID::is_t<Out>(operands[0]),
                    "operands[0] of invalid type; allowed types: ", allowed);

        const bool sym { flat_sym(operands) };
        if constexpr (std::is_same_v<Expr::Bool, Out>) {
            return simplify(
                Expr::factory<Out>(sym, Op::factory<OpT>(std::move(operands)), std::move(sp)));
        }
        else {
            const U64 len { Expr::get_bit_length(operands[0]) }; // Before move
            return simplify(
                Expr::factory<Out>(sym, Op::factory<OpT>(std::move(operands)), len, std::move(sp)));
        }
    }

    /** Using SizeMode SM determine the size of an op containing v */
    template <SizeMode SM> U64 get_size(const Op::FlatArgs &v) {
        if constexpr (SM == SizeMode::First) {
            return Expr::get_bit_length(v[0]);
        }
        else if constexpr (SM == SizeMode::Add) {
            U64 len { 0 };
            for (const auto &i : v) {
                len += Expr::get_bit_length(i);
            }
            return len;
        }
        else {
            static_assert(Util::CD::false_<SM>, "Unsupported size mode");
        }
    }

    /** Create a Expr with a flat op
     *  Out type is the same as operands[0]
     *  Expr pointers may not be nullptr
     */
    template <typename OpT, SizeMode SM, typename... Allowed>
    inline Expr::BasePtr flat(Op::FlatArgs &&operands, Annotation::SPAV &&sp) {
        using namespace Simplify;
        namespace Err = Error::Expr;

        // For speed
        if constexpr (sizeof...(Allowed) == 1) {
            return flat_explicit<Allowed..., OpT, Allowed...>(std::move(operands), std::move(sp));
        }

        // Checks
        static_assert(Op::is_flat<OpT>, "Create::Private::flat requires OpT to be flat");
        UTIL_ASSERT(Err::Size, operands.size() >= 2, "operands are empty.");
        UTIL_ASSERT_NOT_NULL_DEBUG(operands[0]);
        const bool type_ok { CUID::is_any_t<const Expr::Base, Allowed...>(operands[0]) };
        UTIL_ASSERT(Err::Type, type_ok, "operands[0] is the wrong type");

        // Create Expr
        const bool sym { flat_sym(operands) };
        if constexpr (Util::Type::Is::in<Expr::Bool, Allowed...>) {
            if (CUID::is_t<Expr::Bool>(operands[0])) {
                return simplify(Expr::factory<Expr::Bool>(
                    sym, Op::factory<OpT>(std::move(operands)), std::move(sp)));
            }
        }
        const U64 len { get_size<SM>(operands) }; // Before move
        return simplify(Expr::factory_cuid(
            operands[0]->cuid, sym, Op::factory<OpT>(std::move(operands)), len, std::move(sp)));
    }

    /** Create a Expr with a flat op
     *  Out type is the same as operands[0]
     *  Expr pointers may not be nullptr
     *  SizeMode is assumed to be First
     */
    template <typename OpT, typename... Allowed>
    inline Expr::BasePtr flat(Op::FlatArgs &&operands, Annotation::SPAV &&sp) {
        return flat<OpT, SizeMode::First, Allowed...>(std::move(operands), std::move(sp));
    }

} // namespace Create::Private

#endif
