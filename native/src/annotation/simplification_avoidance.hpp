/**
 * @file
 * @brief This file defines the Annotation::SimplificationAvoidance class
 */
#ifndef __ANNOTATION_SIMPLIFICATION_AVOIDANCE_HPP__
#define __ANNOTATION_SIMPLIFICATION_AVOIDANCE_HPP__

#include "base.hpp"


namespace Annotation {

    /** A built-in annotation */
    class SimplificationAvoidance final : public Base {
        FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(Base)
      public:
        /** Constructor */
        SimplificationAvoidance();

        /** Returns whether this annotation can be eliminated in a simplification. */
        inline bool eliminatable() const final override { return false; }

        /** Returns whether this annotation can be relocated in a simplification. */
        inline bool relocatable() const final override { return false; }
    };

} // namespace Annotation

#endif
