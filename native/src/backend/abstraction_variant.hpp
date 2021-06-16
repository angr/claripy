/**
 * @file
 * @brief This file defines the abstract variant type
 */
#ifndef R_BACKEND_ABSTRACTVARIANT_HPP_
#define R_BACKEND_ABSTRACTVARIANT_HPP_

#include "../expression.hpp"
#include "../mode.hpp"

#include <variant>


namespace Backend::Private {

    /** The types claricpp may extract backend objects into */
    using AbstractionVariant = std::variant<Expression::BasePtr, Mode::FP::Rounding, unsigned>;
} // namespace Backend::Private

#endif
