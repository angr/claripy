/**
 * @file
 * @brief This file defines a method to create Exprs with standard binary ops
 */
#ifndef R_SRC_CREATE_PRIVATE_UINTBINARY_HPP_
#define R_SRC_CREATE_PRIVATE_UINTBINARY_HPP_

#include "size_mode.hpp"

#include "../constants.hpp"


namespace Create::Private {

    /** Calculates the length a uint binary expression should have */
    template <SizeMode Mode, typename IntT> U64 uint_len(const IntT i, const Expr::BasePtr &e) {
        if constexpr (Mode == SizeMode::Second) {
            return i;
        }
        else if constexpr (Mode == SizeMode::Add) {
            return i + Expr::get_bit_length(e);
        }
        else {
            static_assert(Util::CD::false_<Mode>, "Unsupported SizeMode");
        }
    }

    /** Create a Expr with a uint binary op
     *  Expr pointers may not be nullptr
     *  Output type is assumed to be BV
     */
    template <typename IntT, typename OpT, SizeMode Mode, typename... Allowed>
    inline Expr::BasePtr uint_binary(const Expr::BasePtr &expr, const IntT integer,
                                     Annotation::SPAV &&sp) {
        static const Expr::TypeNames<Allowed...> allowed;
        using namespace Simplify;
        namespace Err = Error::Expr;

        // Static checks
        static_assert(Util::Type::Is::in<IntT, U64, I64>,
                      "Create::Private::uint_binary requires IntT be either U64 or I64");
        static_assert(Op::is_uint_binary<OpT>,
                      "Create::Private::uint_binary requires a int binary OpT");

        // Dynamic checks
        UTIL_ASSERT(Err::Usage, expr, "Expr cannot be nullptr");
        const bool type_ok { CUID::is_any_t<const Expr::Base, Allowed...>(expr) };
        UTIL_ASSERT(Err::Type, type_ok, "Expr operand of invalid type; allowed types: ", allowed);

        // Construct expr (static casts are safe because of previous checks)
        return simplify(Expr::factory<Expr::BV>(expr->symbolic, Op::factory<OpT>(expr, integer),
                                                uint_len<Mode>(integer, expr), std::move(sp)));
    }

} // namespace Create::Private

#endif
