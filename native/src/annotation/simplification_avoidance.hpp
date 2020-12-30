/**
 * @file
 * @brief This file defines the Annotation::SimplificationAvoidance class
 */
#ifndef __ANNOTATION_SIMPLIFICATION_AVOIDANCE_HPP__
#define __ANNOTATION_SIMPLIFICATION_AVOIDANCE_HPP__

#include "base.hpp"


namespace Annotation {

    /** A built-in annotation */
    class SimplificationAvoidance : public Base {

        /** Returns whether this annotation can be eliminated in a simplification. */
        bool eliminatable() const;

        /** Returns whether this annotation can be relocated in a simplification. */
        bool relocatable() const;
    };

} // namespace Annotation

#endif
