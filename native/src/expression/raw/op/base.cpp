/** @file */
#include "base.hpp"


// For brevity
using namespace Expression;
using namespace Raw;

Op::Base::~Base() {}

// Note that this constructor should never be called because of the diamond problem.
Op::Base::Base() {}
