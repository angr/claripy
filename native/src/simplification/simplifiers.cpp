/** @file */
#include "simplifiers.hpp"

#include "../expression.hpp"
#include "../op.hpp"


// For clarity
using namespace Simplification;
using OP = Op::Operation;


/** @todo */
Expression::Base Simplifier::if_(const Expression::Base &original) {
    /* Expression::Bool = Expression::cast_throw_on_fail<Expression::Bool>(original->args[0]); */

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
Expression::Base Simplifier::concat(const Expression::Base &original) {
    return original; // todo
}

/** @todo */
Expression::Base Simplifier::BV::reverse(const Expression::Base &original) {
    return original; // todo
}

/************************************************/
/*                    Shift                     */
/************************************************/

/** @todo */
Expression::Base Simplifier::Shift::r(const Expression::Base &original) {
    return original; // todo
}

/** @todo */
Expression::Base Simplifier::Shift::l(const Expression::Base &original) {
    return original; // todo
}

/** @todo */
Expression::Base Simplifier::Shift::lshr(const Expression::Base &original) {
    return original; // todo
}

/************************************************/
/*                   Equality                   */
/************************************************/

/** @todo */
Expression::Base Simplifier::eq(const Expression::Base &original) {
    return original; // todo
}

/** @todo */
Expression::Base Simplifier::ne(const Expression::Base &original) {
    return original; // todo
}

/************************************************/
/*                   Boolean                    */
/************************************************/

/** @todo */
Expression::Base Simplifier::Boolean::and_(const Expression::Base &original) {
    return original; // todo
}

/** @todo */
Expression::Base Simplifier::Boolean::or_(const Expression::Base &original) {
    return original; // todo
}

/** @todo */
Expression::Base Simplifier::Boolean::not_(const Expression::Base &original) {
    return original; // todo
}

/************************************************/
/*                   Bitwise                    */
/************************************************/

/** @todo */
Expression::Base Simplifier::Bitwise::add(const Expression::Base &original) {
    return original; // todo
}

/** @todo */
Expression::Base Simplifier::Bitwise::mul(const Expression::Base &original) {
    return original; // todo
}

/** @todo */
Expression::Base Simplifier::Bitwise::sub(const Expression::Base &original) {
    return original; // todo
}

/** @todo */
Expression::Base Simplifier::Bitwise::xor_minmax(const Expression::Base &original) {
    return original; // todo
}

/** @todo */
Expression::Base Simplifier::Bitwise::or_(const Expression::Base &original) {
    return original; // todo
}

/** @todo */
Expression::Base Simplifier::Bitwise::and_(const Expression::Base &original) {
    return original; // todo
}

/** @todo */
Expression::Base Simplifier::Bitwise::xor_(const Expression::Base &original) {
    return original; // todo
}
