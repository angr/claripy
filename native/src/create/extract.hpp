/**
 * @file
 * @brief This file defines a method to create an Expr with an Eq Op
 */
#ifndef R_SRC_CREATE_EXTRACT_HPP_
#define R_SRC_CREATE_EXTRACT_HPP_

#include "constants.hpp"


namespace Create {

    /** Create an Expr with an Extract op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr extract(const U64 high, const U64 low, const Expr::BasePtr &from,
                                 Annotation::SPAV sp = empty_spav) {
        namespace E = Error::Expr;
        using namespace Simplify;

        // Checks
        UTIL_ASSERT(E::Usage, from != nullptr, "from may not be nullptr");
        UTIL_ASSERT(E::Type, CUID::is_t<Expr::BV>(from), "from operands must be an Expr::BV");
        UTIL_ASSERT(E::Type, high >= low, "high must be >= low");

        // Construct expr
        return simplify(Expr::factory<Expr::BV>(from->symbolic,
                                                Op::factory<Op::Extract>(high, low, from),
                                                high + 1 - low, std::move(sp)));
    }

} // namespace Create

#endif
