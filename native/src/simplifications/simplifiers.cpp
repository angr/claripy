/** @file */
#include "simplifiers.hpp"

#include "../ast/raw_types/base.hpp"
#include "../ast/raw_types/bool.hpp"
#include "../ops/operations.hpp"


// For clarity
using namespace Simplifications;
using Op = Ops::Operation;

/** @todo */
AST::Base Simplifiers::if_(const AST::Base &original) {
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
AST::Base Simplifiers::concat(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Simplifiers::BV::reverse(const AST::Base &original) {
    return original; // todo
}

/************************************************/
/*                    Shift                     */
/************************************************/

/** @todo */
AST::Base Simplifiers::Shift::r(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Simplifiers::Shift::l(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Simplifiers::Shift::lshr(const AST::Base &original) {
    return original; // todo
}

/************************************************/
/*                   Equality                   */
/************************************************/

/** @todo */
AST::Base Simplifiers::eq(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Simplifiers::ne(const AST::Base &original) {
    return original; // todo
}

/************************************************/
/*                   Boolean                    */
/************************************************/

/** @todo */
AST::Base Simplifiers::Boolean::and_(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Simplifiers::Boolean::or_(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Simplifiers::Boolean::not_(const AST::Base &original) {
    return original; // todo
}

/************************************************/
/*                   Bitwise                    */
/************************************************/

/** @todo */
AST::Base Simplifiers::Bitwise::add(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Simplifiers::Bitwise::mul(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Simplifiers::Bitwise::sub(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Simplifiers::Bitwise::xor_minmax(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Simplifiers::Bitwise::or_(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Simplifiers::Bitwise::and_(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Simplifiers::Bitwise::xor_(const AST::Base &original) {
    return original; // todo
}
