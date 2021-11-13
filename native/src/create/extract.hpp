/**
 * @file
 * @brief This file defines a method to create an Expr with an Eq Op
 */
#ifndef R_CREATE_EXTRACT_HPP_
#define R_CREATE_EXTRACT_HPP_

#include "constants.hpp"


namespace Create {

    /** Create an Expr with an Extract op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr extract(const UInt high, const UInt low, const Expr::BasePtr &from,
                                 Annotation::SPAV &&sp = nullptr) {
        namespace E = Error::Expr;
        using namespace Simplification;

        // Checks
        Util::affirm<E::Usage>(from != nullptr, WHOAMI "from may not be nullptr");
        Util::affirm<E::Type>(CUID::is_t<Expr::BV>(from),
                              WHOAMI "from operands must be an Expr::BV");
        Util::affirm<E::Type>(high >= low, WHOAMI "high must be >= low");

        // Construct expr
        return simplify(Expr::factory<Expr::BV>(from->symbolic,
                                                Op::factory<Op::Extract>(high, low, from),
                                                high + 1 - low, std::move(sp)));
    }

} // namespace Create

#endif
