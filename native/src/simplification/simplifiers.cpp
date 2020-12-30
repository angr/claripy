/** @file */
#include "simplifiers.hpp"

#include "../ast/raw_types/base.hpp"
#include "../ast/raw_types/bool.hpp"
#include "../op.hpp"


// For clarity
using namespace Simplification;
using OP = Op::Operation;

/** @todo */
AST::Base Simplifier::if_(const AST::Base &original) {
    /* AST::Bool = AST::cast_throw_on_fail<AST::Bool>(original->args[0]); */

    /* if (cond->is_true()) { */
    /* return if_true; */
    /* } */
    /* else if (cond->is_false()) { */
    /* return if_false; */
    /* } */
    /* else { */
    /* return original; */
    /* } */
    return original;
}

/** @todo */
AST::Base Simplifier::concat(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Simplifier::BV::reverse(const AST::Base &original) {
    return original; // todo
}

/************************************************/
/*                    Shift                     */
/************************************************/

/** @todo */
AST::Base Simplifier::Shift::r(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Simplifier::Shift::l(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Simplifier::Shift::lshr(const AST::Base &original) {
    return original; // todo
}

/************************************************/
/*                   Equality                   */
/************************************************/

/** @todo */
AST::Base Simplifier::eq(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Simplifier::ne(const AST::Base &original) {
    return original; // todo
}

/************************************************/
/*                   Boolean                    */
/************************************************/

/** @todo */
AST::Base Simplifier::Boolean::and_(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Simplifier::Boolean::or_(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Simplifier::Boolean::not_(const AST::Base &original) {
    return original; // todo
}

/************************************************/
/*                   Bitwise                    */
/************************************************/

/** @todo */
AST::Base Simplifier::Bitwise::add(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Simplifier::Bitwise::mul(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Simplifier::Bitwise::sub(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Simplifier::Bitwise::xor_minmax(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Simplifier::Bitwise::or_(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Simplifier::Bitwise::and_(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Simplifier::Bitwise::xor_(const AST::Base &original) {
    return original; // todo
}
