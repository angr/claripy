/** @file */
#include "simplification_avoidance.hpp"


// For clarity
using namespace Annotation;

Constants::CCS SimplificationAvoidance::hash() const {
    return typeid(SimplificationAvoidance).name();
}

bool SimplificationAvoidance::eliminatable() const {
    return false;
}

bool SimplificationAvoidance::relocatable() const {
    return false;
}
