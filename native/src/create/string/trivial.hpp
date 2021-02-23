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
        namespace CP = ::Create::Private;
        return CP::unary<Ex::Bool, Ex::String, Op::String::IsDigit, Ex::String>(
            std::forward<EAnVec>(av), x);
    }

    /********************************************************************/
    /*                 Int Binary Passthrough Functions                 */
    /********************************************************************/

    /** Create an Expression with an String::SignExt op
     *  Note: Currently Ints are taken in as BVs
     */
    inline EBasePtr to_int(EAnVec &&av, const EBasePtr &expr, const Constants::UInt integer) {
        namespace Ex = Expression;
        namespace CP = ::Create::Private;
        return CP::int_binary<Constants::UInt, Ex::BV, Ex::String, Op::String::ToInt,
                              CP::SizeMode::Second, Ex::String>(std::forward<EAnVec>(av), expr,
                                                                integer);
    }

    /** Create an Expression with an String::Len op
     *  Note: Currently Ints are output as BVs
     */
    inline EBasePtr len(EAnVec &&av, const EBasePtr &expr, const Constants::UInt integer) {
        namespace Ex = Expression;
        namespace CP = ::Create::Private;
        return CP::int_binary<Constants::UInt, Ex::BV, Ex::String, Op::String::Len,
                              CP::SizeMode::Second, Ex::String>(std::forward<EAnVec>(av), expr,
                                                                integer);
    }

    /********************************************************************/
    /*                   Binary Passthrough Functions                   */
    /********************************************************************/

    /** Create an Expression with a String::Contains op */
    inline EBasePtr contains(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        namespace CP = ::Create::Private;
        return CP::binary<Ex::Bool, Ex::String, Op::String::Contains, CP::SizeMode::NA,
                          Ex::String>(std::forward<EAnVec>(av), left, right);
    }

    /** Create an Expression with a String::PrefixOf op */
    inline EBasePtr prefix_of(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        namespace CP = ::Create::Private;
        return CP::binary<Ex::Bool, Ex::String, Op::String::PrefixOf, CP::SizeMode::NA,
                          Ex::String>(std::forward<EAnVec>(av), left, right);
    }

    /** Create an Expression with a String::SuffixOf op */
    inline EBasePtr suffix_of(EAnVec &&av, const EBasePtr &left, const EBasePtr &right) {
        namespace Ex = Expression;
        namespace CP = ::Create::Private;
        return CP::binary<Ex::Bool, Ex::String, Op::String::SuffixOf, CP::SizeMode::NA,
                          Ex::String>(std::forward<EAnVec>(av), left, right);
    }

} // namespace Create::String

#endif
