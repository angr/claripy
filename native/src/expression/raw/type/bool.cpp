/** @file */
#include "bool.hpp"

#include "../../../utils.hpp"


// For clarity
using namespace Expression::Raw;
using namespace Type;


Bool::~Bool() {}

/** @todo this is a dummy */
bool Bool::is_true() const {
    return true;
}

/** @todo this is a dummy */
bool Bool::is_false() const {
    return true;
}

Constants::CCS Bool::type() const {
    return "Bool";
}
