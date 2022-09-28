/**
 * @file
 * @brief This file defines a method to create an Expr with an Extract Op
 */
#ifndef R_SRC_CREATE_EXTRACT_HPP_
#define R_SRC_CREATE_EXTRACT_HPP_

#include "constants.hpp"


namespace Create {

    /** Create an Expr with an Extract op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr extract(const U64 high, const U64 low, const Expr::BasePtr &from,
                                 Expr::OpPyDict d = {}) {
        UTIL_ASSERT(Error::Expr::Usage, from, "from may not be nullptr");
        UTIL_ASSERT(Error::Expr::Type, CUID::is_t<Expr::BV>(from),
                    "from operands must be an Expr::BV");
        UTIL_ASSERT(Error::Expr::Type, high >= low, "high must be >= low");

        // Construct expr
        return Simplify::simplify(Expr::factory<Expr::BV>(from->symbolic,
                                                          Op::factory<Op::Extract>(high, low, from),
                                                          std::move(d), high + 1 - low));
    }

} // namespace Create

#endif
