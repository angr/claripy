/**
 * @file
 * @brief This file defines the type_name functions for expressions
 * Note that these are not member functions to avoid vtables
 */
#ifndef __EXPRESSION_TYPENAME_HPP__
#define __EXPRESSION_TYPENAME_HPP__

#include "instantiables.hpp"


namespace Expression {

    /** Return the type name of e */
    constexpr Constants::CCSC type_name(const Expression::RawPtr e) {
        switch (e->cuid) {
            case Bool::static_cuid:
                return "Bool";
            case String::static_cuid:
                return "String";
            case BV::static_cuid:
                return "BV";
            case FP::static_cuid:
                return "BV";
            case VS::static_cuid:
                return "BV";
            default:
                throw Utils::Error::Unexpected::Type(WHOAMI_WITH_SOURCE
                                                     "CUID unknown; unknown type.");
        }
    }

    /** Return the type name of e */
    inline Constants::CCSC type_name(const Expression::BasePtr &e) { return type_name(e.get()); }

} // namespace Expression

#endif
