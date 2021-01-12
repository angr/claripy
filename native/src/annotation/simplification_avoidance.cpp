/** @file */
#include "simplification_avoidance.hpp"

#include "../utils.hpp"


// For clarity
using namespace Annotation;


Constants::UInt SimplificationAvoidance::hash() const {
    return Utils::type_id<SimplificationAvoidance>();
}

bool SimplificationAvoidance::eliminatable() const {
    return false;
}

bool SimplificationAvoidance::relocatable() const {
    return false;
}
