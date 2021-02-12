/**
 * @file
 * @brief This file defines a method to create an Expression with an Concat Op
 */
#ifndef __CREATE_CONCAT_HPP__
#define __CREATE_CONCAT_HPP__

#include "constants.hpp"
#include "private/size.hpp"


namespace Create {

    /** Create a Expression with an Concat op */
    template <typename T>
    EBasePtr concat(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {

        // For brevity
        namespace Ex = Expression;
        using namespace Simplification;
        namespace Err = Error::Expression;

        // Static checks
        static_assert(Utils::qualified_is_in<T, Ex::BV, Ex::String>,
                      "Create::concat argument types must be of type BV or String");
        static_assert(std::is_final_v<T>, "Create::concat's assumes T is final");

        // Dynamic checks
        Utils::affirm<Err::Type>(Ex::is_t<T>(left),
                                 "Create::concat left operands must be of type T");
        Utils::affirm<Err::Type>(Ex::is_t<T>(right),
                                 "Create::concat right operands must be of type T");

        // Construct expression (static casts are safe because of previous checks)
        return simplify(Ex::factory<T>(std::forward<EAnVec>(av), left->symbolic || right->symbolic,
                                       Op::factory<Op::Concat>(left, right),
                                       Private::size(left) + Private::size(right)));
    }

} // namespace Create

#endif
