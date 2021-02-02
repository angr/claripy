/** @file */
#include "simplification_avoidance.hpp"

#include "../utils.hpp"


// For clarity
using namespace Annotation;


SimplificationAvoidance::SimplificationAvoidance() : Base(UTILS_FILE_LINE_HASH) {}


bool SimplificationAvoidance::eliminatable() const {
    return false;
}

bool SimplificationAvoidance::relocatable() const {
    return false;
}
