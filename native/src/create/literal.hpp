/**
 * @file
 * @brief This file defines a method to create an Expression with an literal Op
 */
#ifndef __CREATE_LITERAL_HPP__
#define __CREATE_LITERAL_HPP__

#include "private/literal.hpp"


namespace Create {

    /** Create a Bool Expression with a Literal op */
    inline EBasePtr literal(EAnVec &&av, const bool data) {
        return Private::literal<Expression::Bool, bool>(std::move(av), bool { data });
    }

    /** Create a String Expression with a Literal op */
    inline EBasePtr literal(EAnVec &&av, std::string &&data) {
        return Private::literal<Expression::String, std::string>(std::move(av), std::move(data));
    }

    /** Create a BV Expression with a Literal op */
    inline EBasePtr literal(EAnVec &&av, std::vector<char> &&data) {
        return Private::literal<Expression::BV, std::vector<char>>(std::move(av), std::move(data));
    }

    /** Create a FP Expression with a Literal op containing a double precision float */
    inline EBasePtr literal(EAnVec &&av, const double data) {
        return Private::literal<Expression::FP, double>(std::move(av), double { data });
    }

    /** Create a FP Expression with a Literal op containing a single precision float */
    inline EBasePtr literal(EAnVec &&av, const float data) {
        return Private::literal<Expression::FP, float>(std::move(av), float { data });
    }

    /** Create a FP Expression with a Literal op containing a single precision float */
    inline EBasePtr literal(EAnVec &&av, PyObj::VSPtr &&data) {
        return Private::literal<Expression::VS, PyObj::VSPtr>(std::move(av), std::move(data));
    }

} // namespace Create

#endif
