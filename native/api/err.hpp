/**
 * @file
 * @brief This file defines API Errors
 * \ingroup api
 */
#ifndef R_ERR_HPP_
#define R_ERR_HPP_

#include <src/util.hpp>

namespace API::Err {

    /** Claripy Expr exception */
    using Claripy = ::Util::Err::Python::Claripy;

    /** API exception class */
    UTIL_ERR_DEFINE_NONFINAL_EXCEPTION(Base, Claripy);

    /** API usage exception */
    UTIL_ERR_DEFINE_NONFINAL_EXCEPTION(Usage, Base);
} // namespace API::Err

#endif