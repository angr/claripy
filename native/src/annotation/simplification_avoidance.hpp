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

        /** Virtual hash function
         *  Every subclass must implement this
         */
        virtual Constants::UInt hash() const override;

        /** Returns whether this annotation can be eliminated in a simplification. */
        bool eliminatable() const final override;

        /** Returns whether this annotation can be relocated in a simplification. */
        bool relocatable() const final override;
    };

} // namespace Annotation

#endif
