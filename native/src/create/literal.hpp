/**
 * @file
 * @brief This file defines a method to create an Expression with an literal Op
 */
#ifndef R_CREATE_LITERAL_HPP_
#define R_CREATE_LITERAL_HPP_

#include "private/literal.hpp"


namespace Create {

    /** Create a Bool Expression with a Literal op */
    inline EBasePtr literal(const bool data, SPAV &&sp = nullptr) {
        return Private::literal<Expression::Bool, bool>(bool { data }, std::move(sp));
    }

    /** Create a String Expression with a Literal op */
    inline EBasePtr literal(std::string &&data, SPAV &&sp = nullptr) {
        return Private::literal<Expression::String, std::string>(std::move(data), std::move(sp));
    }

    /** Create a BV Expression with a Literal op */
    inline EBasePtr literal(std::vector<char> &&data, SPAV &&sp = nullptr) {
        return Private::literal<Expression::BV, std::vector<char>>(std::move(data), std::move(sp));
    }

    /** Create a FP Expression with a Literal op containing a double precision float */
    inline EBasePtr literal(const double data, SPAV &&sp = nullptr) {
        return Private::literal<Expression::FP, double>(double { data }, std::move(sp));
    }

    /** Create a FP Expression with a Literal op containing a single precision float */
    inline EBasePtr literal(const float data, SPAV &&sp = nullptr) {
        return Private::literal<Expression::FP, float>(float { data }, std::move(sp));
    }

    /** Create a FP Expression with a Literal op containing a single precision float
     *  data may not be nullptr
     */
    inline EBasePtr literal(PyObj::VSPtr &&data, SPAV &&sp = nullptr) {
        return Private::literal<Expression::VS, PyObj::VSPtr>(std::move(data), std::move(sp));
    }

} // namespace Create

#endif
