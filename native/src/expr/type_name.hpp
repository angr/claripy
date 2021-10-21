/**
 * @file
 * @brief This file defines the type_name functions for exprs
 * Note that these are not member functions to avoid vtables
 */
#ifndef R_EXPR_TYPENAME_HPP_
#define R_EXPR_TYPENAME_HPP_

#include "instantiables.hpp"


namespace Expr {

    /** Return the type name of the expr type given by cuid c */
    constexpr const char *type_name(const CUID::CUID c) {
        switch (c) {
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
                throw Util::Err::Type(WHOAMI "CUID unknown; unknown type.");
        }
    }

    /** Return the type name of the expr type */
    template <typename T> constexpr const char *type_name() { return type_name(T::static_cuid); }

    /** Return the type name of the expr pointed to by non-nullptr e */
    constexpr const char *type_name(const Expr::RawPtr e) {
        UTILS_AFFIRM_NOT_NULL_DEBUG(e);
        return type_name(e->cuid);
    }

    /** Return the type name of the expr pointed to by non-nullptr e */
    inline const char *type_name(const Expr::BasePtr &e) { return type_name(e.get()); }

} // namespace Expr

#endif
