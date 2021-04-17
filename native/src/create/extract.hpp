/**
 * @file
 * @brief This file defines a method to create an Expression with an Eq Op
 */
#ifndef __CREATE_EXTRACT_HPP__
#define __CREATE_EXTRACT_HPP__

#include "constants.hpp"


namespace Create {

#warning str_extract_check seems to take different arguments, we ignored that function *for now*

    /** Create an Expression with an Extract op */
    template <typename T>
    EBasePtr extract(EAnVec &&av, const Constants::UInt high, const Constants::UInt low,
                     const Expression::BasePtr &from) {

        // For brevity
        namespace Ex = Expression;
        namespace Err = Error::Expression;
        using namespace Simplification;

        // Checks
        static_assert(Utils::qualified_is_in<T, Ex::String, Ex::BV>,
                      "T must be either a BV or String");
        Utils::affirm<Err::Type>(CUID::is_t<T>(from),
                                 WHOAMI_WITH_SOURCE "from operands must be a T");
        Utils::affirm<Err::Type>(high >= low,
                                 WHOAMI_WITH_SOURCE "high should not be lower than low");

        // Construct expression
        return simplify(Ex::factory<T>(std::forward<EAnVec>(av), from->symbolic,
                                       Op::factory<Op::Extract>(high, low, from), high + 1 - low));
    }

} // namespace Create

#endif
