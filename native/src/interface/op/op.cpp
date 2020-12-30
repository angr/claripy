/** @file */
#include "op.hpp"


// For brevity
using namespace Interface;

Op::Op::Op(const AST::Base & b, const Ops::Operation o) : Base(b), op(o) {}
