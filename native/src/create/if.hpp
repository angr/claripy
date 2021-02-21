/**
 * @file
 * @brief This file defines a method to create an Expression with an Eq Op
 */
#ifndef __CREATE_IF_HPP__
#define __CREATE_IF_HPP__

#include "constants.hpp"
#include "private/bit_length.hpp"


namespace Create {

    /** Create an Expression with an If op */
    template <typename T>
    EBasePtr if_(EAnVec &&av, const EBasePtr &cond, const EBasePtr &left, const EBasePtr &right) {

        // For brevity
        namespace Ex = Expression;
        namespace Err = Error::Expression;
        using namespace Simplification;

        // Type checks
        static_assert(Utils::is_ancestor<Expression::Base, T>, "T must subclass Expression::Base");
        Utils::affirm<Err::Type>(Ex::is_t<T>(left),
                                 WHOAMI_WITH_SOURCE "left operands must be a T");

        // Construct expression
        const bool sym { cond->symbolic || left->symbolic || right->symbolic };
        auto op { Op::factory<Op::If>(cond, left, right) };
        if constexpr (Utils::is_ancestor<Expression::Bits, T>) {
            // static cast is safe because we verified left is a T
            return simplify(Ex::factory<T>(std::forward<EAnVec>(av), sym, std::move(op),
                                           Private::bit_length(left)));
        }
        else {
            return simplify(Ex::factory<T>(std::forward<EAnVec>(av), sym, std::move(op)));
        }
    }

} // namespace Create

#endif
