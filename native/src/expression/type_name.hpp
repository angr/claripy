/**
 * @file
 * @brief This file defines the type_name functions for expressions
 * Note that these are not member functions to avoid vtables
 */
#ifndef R_EXPRESSION_TYPENAME_HPP_
#define R_EXPRESSION_TYPENAME_HPP_

#include "instantiables.hpp"


namespace Expression {

    /** Return the type name of the expression pointed to by non-nullptr e */
    constexpr const char *type_name(const Expression::RawPtr e) {
        UTILS_AFFIRM_NOT_NULL_DEBUG(e);
        switch (e->cuid) {
            case Bool::static_cuid:
                return "Bool";
            case String::static_cuid:
                return "String";
            case BV::static_cuid:
                return "BV";
            case FP::static_cuid:
                return "FP";
            case VS::static_cuid:
                return "VS";
            default:
                throw Utils::Error::Unexpected::Type(WHOAMI_WITH_SOURCE
                                                     "CUID unknown; unknown type.");
        }
    }

    /** Return the type name of the expression pointed to by non-nullptr e */
    inline const char *type_name(const Expression::BasePtr &e) { return type_name(e.get()); }

} // namespace Expression

#endif
