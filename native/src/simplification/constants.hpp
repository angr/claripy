/**
 * @file
 * @brief This file contains constants used within the simplifications directory
 */
#ifndef __SIMPLIFICATION_CONSTANTS_HPP__
#define __SIMPLIFICATION_CONSTANTS_HPP__

#include "../expression.hpp"


namespace Simplification {

    /** The type each top level simplifier must have */
    using SimplifierFunc = Factory::Ptr<Expression::Base>(const Factory::Ptr<Expression::Base> &);

} // namespace Simplification

#endif
