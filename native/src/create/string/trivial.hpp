/**
 * @file
 * @brief This file defines a group of create methods for trivial passthrough string ops
 */
#ifndef __CREATE_STRING_TRIVIAL_HPP__
#define __CREATE_STRING_TRIVIAL_HPP__

#include "../private/binary.hpp"
#include "../private/int_binary.hpp"
#include "../private/unary.hpp"


namespace Create::String {

    /********************************************************************/
    /*                   Unary Passthrough Functions                    */
    /********************************************************************/

    /** Create a bool Expression with an String::IsDigit op */
    inline EBasePtr is_digit(EAnVec &&av, const EBasePtr &x) {
        namespace Ex = Expression;
        return Private::unary<Ex::Bool, Ex::String, Op::String::IsDigit, Ex::String>(
            std::forward<EAnVec>(av), x);
    }

    /********************************************************************/
    /*                 Int Binary Passthrough Functions                 */
    /********************************************************************/

    /** Create an Expression with an String::SignExt op */
    inline EBasePtr to_int(EAnVec &&av, const EBasePtr &expr, const Constants::UInt integer) {
        namespace Ex = Expression;
        return Private::int_binary<Constants::UInt, Ex::BV, Ex::String, Op::String::ToInt,
                                   Private::SizeMode::Second, Ex::String>(std::forward<EAnVec>(av),
                                                                          expr, integer);
    }

    /** Create an Expression with an String::Len op */
    inline EBasePtr len(EAnVec &&av, const EBasePtr &expr, const Constants::UInt integer) {
        namespace Ex = Expression;
        return Private::int_binary<Constants::UInt, Ex::BV, Ex::String, Op::String::Len,
                                   Private::SizeMode::Second, Ex::String>(std::forward<EAnVec>(av),
                                                                          expr, integer);
    }

    /********************************************************************/
    /*                   Binary Passthrough Functions                   */
    /********************************************************************/

    /** Create an Expression with a String::Contains op */
    inline EBasePtr contains(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<Ex::Bool, Ex::String, Op::String::Contains, Private::SizeMode::NA,
                               Ex::String>(std::forward<EAnVec>(av), left, right);
    }

    /** Create an Expression with a String::Contains op */
    inline EBasePtr prefix_of(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<Ex::Bool, Ex::String, Op::String::PrefixOf, Private::SizeMode::NA,
                               Ex::String>(std::forward<EAnVec>(av), left, right);
    }

    /** Create an Expression with a String::Contains op */
    inline EBasePtr suffix_of(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        return Private::binary<Ex::Bool, Ex::String, Op::String::SuffixOf, Private::SizeMode::NA,
                               Ex::String>(std::forward<EAnVec>(av), left, right);
    }

} // namespace Create::String

#endif
