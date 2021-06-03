/** @file */
#include "simplifiers.hpp"

#include "../op.hpp"


// For clarity
using namespace Simplification;


/** @todo
 *  original may not be nullptr
 */
Expression::BasePtr Simplifier::if_(const Expression::BasePtr &original) {
    UTILS_AFFIRM_NOT_NULL_DEBUG(original);
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

/** @todo
 *  original may not be nullptr
 */
Expression::BasePtr Simplifier::concat(const Expression::BasePtr &original) {
    UTILS_AFFIRM_NOT_NULL_DEBUG(original);
    return original; // todo
}

/** @todo
 *  original may not be nullptr
 */
Expression::BasePtr Simplifier::BV::reverse(const Expression::BasePtr &original) {
    UTILS_AFFIRM_NOT_NULL_DEBUG(original);
    return original; // todo
}

/************************************************/
/*                    Shift                     */
/************************************************/

/** @todo
 *  original may not be nullptr
 */
Expression::BasePtr Simplifier::Shift::r(const Expression::BasePtr &original) {
    UTILS_AFFIRM_NOT_NULL_DEBUG(original);
    return original; // todo
}

/** @todo
 *  original may not be nullptr
 */
Expression::BasePtr Simplifier::Shift::l(const Expression::BasePtr &original) {
    return original; // todo
}

/** @todo
 *  original may not be nullptr
 */
Expression::BasePtr Simplifier::Shift::lshr(const Expression::BasePtr &original) {
    return original; // todo
}

/************************************************/
/*                   Equality                   */
/************************************************/

/** @todo
 *  original may not be nullptr
 */
Expression::BasePtr Simplifier::eq(const Expression::BasePtr &original) {
#ifdef DEBUG
    UTILS_AFFIRM_NOT_NULL_DEBUG(original);
    Utils::dynamic_test_throw_on_fail<Op::Eq, Utils::Error::Unexpected::Type>(
        original->op, "Simplifer::eq's Expression's op must be an Op::Eq");
#endif
    Utils::Log::verbose("Eq simplifier invoked");
    return original; // todo
}

/** @todo
 *  original may not be nullptr
 */
Expression::BasePtr Simplifier::ne(const Expression::BasePtr &original) {
    UTILS_AFFIRM_NOT_NULL_DEBUG(original);
    return original; // todo
}

/************************************************/
/*                   Boolean                    */
/************************************************/

/** @todo
 *  original may not be nullptr
 */
Expression::BasePtr Simplifier::Boolean::and_(const Expression::BasePtr &original) {
    UTILS_AFFIRM_NOT_NULL_DEBUG(original);
    return original; // todo
}

/** @todo
 *  original may not be nullptr
 */
Expression::BasePtr Simplifier::Boolean::or_(const Expression::BasePtr &original) {
    UTILS_AFFIRM_NOT_NULL_DEBUG(original);
    return original; // todo
}

/** @todo
 *  original may not be nullptr
 */
Expression::BasePtr Simplifier::Boolean::not_(const Expression::BasePtr &original) {
    UTILS_AFFIRM_NOT_NULL_DEBUG(original);
    return original; // todo
}

/************************************************/
/*                   Bitwise                    */
/************************************************/

/** @todo
 *  original may not be nullptr
 */
Expression::BasePtr Simplifier::Bitwise::add(const Expression::BasePtr &original) {
    UTILS_AFFIRM_NOT_NULL_DEBUG(original);
    return original; // todo
}

/** @todo
 *  original may not be nullptr
 */
Expression::BasePtr Simplifier::Bitwise::mul(const Expression::BasePtr &original) {
    UTILS_AFFIRM_NOT_NULL_DEBUG(original);
    return original; // todo
}

/** @todo
 *  original may not be nullptr
 */
Expression::BasePtr Simplifier::Bitwise::sub(const Expression::BasePtr &original) {
    UTILS_AFFIRM_NOT_NULL_DEBUG(original);
    return original; // todo
}

/** @todo
 *  original may not be nullptr
 */
Expression::BasePtr Simplifier::Bitwise::xor_minmax(const Expression::BasePtr &original) {
    UTILS_AFFIRM_NOT_NULL_DEBUG(original);
    return original; // todo
}

/** @todo
 *  original may not be nullptr
 */
Expression::BasePtr Simplifier::Bitwise::or_(const Expression::BasePtr &original) {
    UTILS_AFFIRM_NOT_NULL_DEBUG(original);
    return original; // todo
}

/** @todo
 *  original may not be nullptr
 */
Expression::BasePtr Simplifier::Bitwise::and_(const Expression::BasePtr &original) {
    UTILS_AFFIRM_NOT_NULL_DEBUG(original);
    return original; // todo
}

/** @todo
 *  original may not be nullptr
 */
Expression::BasePtr Simplifier::Bitwise::xor_(const Expression::BasePtr &original) {
    UTILS_AFFIRM_NOT_NULL_DEBUG(original);
    return original; // todo
}
