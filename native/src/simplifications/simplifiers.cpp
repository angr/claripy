/** @file */
#include "simplifiers.hpp"

#include "../ast/raw_types/base.hpp"
#include "../ast/raw_types/bool.hpp"
#include "../ops/operations_enum.hpp"


// For clarity
using namespace Simplifications::Simplifiers;
using Op = Ops::Operation;

/** @todo */
AST::Base if_(const AST::Base &original) {
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
AST::Base concat(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base bv_reverse(const AST::Base &original) {
    return original; // todo
}

/************************************************/
/*                    Shift                     */
/************************************************/

/** @todo */
AST::Base Shift::r(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Shift::l(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Shift::lshr(const AST::Base &original) {
    return original; // todo
}

/************************************************/
/*                   Equality                   */
/************************************************/

/** @todo */
AST::Base eq(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base ne(const AST::Base &original) {
    return original; // todo
}

/************************************************/
/*                   Boolean                    */
/************************************************/

/** @todo */
AST::Base Boolean::and_(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Boolean::or_(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Boolean::not_(const AST::Base &original) {
    return original; // todo
}

/************************************************/
/*                   Bitwise                    */
/************************************************/

/** @todo */
AST::Base Bitwise::add(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Bitwise::mul(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Bitwise::sub(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Bitwise::xor_minmax(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Bitwise::or_(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Bitwise::and_(const AST::Base &original) {
    return original; // todo
}

/** @todo */
AST::Base Bitwise::xor_(const AST::Base &original) {
    return original; // todo
}
