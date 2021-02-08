/** @file */
#include "simplifiers.hpp"


// For clarity
using namespace Simplification;


/** @todo */
Factory::Ptr<Expression::Base> Simplifier::if_(const Factory::Ptr<Expression::Base> &original) {
    /* Expression::Bool { Expression::cast_throw_on_fail<Expression::Bool>(original->args[0]) }; */

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
Factory::Ptr<Expression::Base> Simplifier::concat(const Factory::Ptr<Expression::Base> &original) {
    return original; // todo
}

/** @todo */
Factory::Ptr<Expression::Base>
Simplifier::BV::reverse(const Factory::Ptr<Expression::Base> &original) {
    return original; // todo
}

/************************************************/
/*                    Shift                     */
/************************************************/

/** @todo */
Factory::Ptr<Expression::Base>
Simplifier::Shift::r(const Factory::Ptr<Expression::Base> &original) {
    return original; // todo
}

/** @todo */
Factory::Ptr<Expression::Base>
Simplifier::Shift::l(const Factory::Ptr<Expression::Base> &original) {
    return original; // todo
}

/** @todo */
Factory::Ptr<Expression::Base>
Simplifier::Shift::lshr(const Factory::Ptr<Expression::Base> &original) {
    return original; // todo
}

/************************************************/
/*                   Equality                   */
/************************************************/

/** @todo */
Factory::Ptr<Expression::Base> Simplifier::eq(const Factory::Ptr<Expression::Base> &original) {
    Utils::Log::verbose("Eq simplifier invoked");
    return original; // todo
}

/** @todo */
Factory::Ptr<Expression::Base> Simplifier::ne(const Factory::Ptr<Expression::Base> &original) {
    return original; // todo
}

/************************************************/
/*                   Boolean                    */
/************************************************/

/** @todo */
Factory::Ptr<Expression::Base>
Simplifier::Boolean::and_(const Factory::Ptr<Expression::Base> &original) {
    return original; // todo
}

/** @todo */
Factory::Ptr<Expression::Base>
Simplifier::Boolean::or_(const Factory::Ptr<Expression::Base> &original) {
    return original; // todo
}

/** @todo */
Factory::Ptr<Expression::Base>
Simplifier::Boolean::not_(const Factory::Ptr<Expression::Base> &original) {
    return original; // todo
}

/************************************************/
/*                   Bitwise                    */
/************************************************/

/** @todo */
Factory::Ptr<Expression::Base>
Simplifier::Bitwise::add(const Factory::Ptr<Expression::Base> &original) {
    return original; // todo
}

/** @todo */
Factory::Ptr<Expression::Base>
Simplifier::Bitwise::mul(const Factory::Ptr<Expression::Base> &original) {
    return original; // todo
}

/** @todo */
Factory::Ptr<Expression::Base>
Simplifier::Bitwise::sub(const Factory::Ptr<Expression::Base> &original) {
    return original; // todo
}

/** @todo */
Factory::Ptr<Expression::Base>
Simplifier::Bitwise::xor_minmax(const Factory::Ptr<Expression::Base> &original) {
    return original; // todo
}

/** @todo */
Factory::Ptr<Expression::Base>
Simplifier::Bitwise::or_(const Factory::Ptr<Expression::Base> &original) {
    return original; // todo
}

/** @todo */
Factory::Ptr<Expression::Base>
Simplifier::Bitwise::and_(const Factory::Ptr<Expression::Base> &original) {
    return original; // todo
}

/** @todo */
Factory::Ptr<Expression::Base>
Simplifier::Bitwise::xor_(const Factory::Ptr<Expression::Base> &original) {
    return original; // todo
}
