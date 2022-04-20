/**
 * @file
 * @brief This file defines a method to copy an expr but change the annotations
 */
#ifndef R_SRC_EXPR_MAKELIKE_HPP_
#define R_SRC_EXPR_MAKELIKE_HPP_

#include "base.hpp"


namespace Expr {

    /** Copy the expr, but use the newly provided annotation vector
     *  in may not be nullptr
     */
    BasePtr make_like(const BasePtr &in, Annotation::SPAV &&sp);

} // namespace Expr

#endif
