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
        namespace Ex = Expr;
        namespace Err = Error::Expr;
        using namespace Simplification;

        // Checks
        Util::affirm<Err::Usage>(from != nullptr, WHOAMI_WITH_SOURCE "from may not be nullptr");
        Util::affirm<Err::Type>(CUID::is_t<Ex::BV>(from),
                                WHOAMI_WITH_SOURCE "from operands must be an Expr::BV");
        Util::affirm<Err::Type>(high >= low,
                                WHOAMI_WITH_SOURCE "high should not be lower than low");

        // Construct expr
        return simplify(Ex::factory<Ex::BV>(from->symbolic,
                                            Op::factory<Op::Extract>(high, low, from),
                                            high + 1 - low, std::move(sp)));
    }

} // namespace Create

#endif
