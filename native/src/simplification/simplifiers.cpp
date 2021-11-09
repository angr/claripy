/** @file */
#include "simplifiers.hpp"

#include "../op.hpp"


// For clarity
using namespace Simplification;


/** @todo
 *  original may not be nullptr
 */
Expr::BasePtr Simplifier::if_(const Expr::BasePtr &original) {
    UTIL_AFFIRM_NOT_NULL_DEBUG(original);
    /* Expr::Bool { Expr::cast_throw_on_fail<Expr::Bool>(original->args[0]) }; */

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
Expr::BasePtr Simplifier::concat(const Expr::BasePtr &original) {
    UTIL_AFFIRM_NOT_NULL_DEBUG(original);
    return original; // todo
}

/** @todo
 *  original may not be nullptr
 */
Expr::BasePtr Simplifier::BV::reverse(const Expr::BasePtr &original) {
    UTIL_AFFIRM_NOT_NULL_DEBUG(original);
    return original; // todo
}

/************************************************/
/*                    Shift                     */
/************************************************/

/** @todo
 *  original may not be nullptr
 */
Expr::BasePtr Simplifier::Shift::r(const Expr::BasePtr &original) {
    UTIL_AFFIRM_NOT_NULL_DEBUG(original);
    return original; // todo
}

/** @todo
 *  original may not be nullptr
 */
Expr::BasePtr Simplifier::Shift::l(const Expr::BasePtr &original) {
    return original; // todo
}

/** @todo
 *  original may not be nullptr
 */
Expr::BasePtr Simplifier::Shift::lshr(const Expr::BasePtr &original) {
    return original; // todo
}

/************************************************/
/*                   Equality                   */
/************************************************/

/** @todo
 *  original may not be nullptr
 */
Expr::BasePtr Simplifier::eq(const Expr::BasePtr &original) {
#ifdef DEBUG
    UTIL_AFFIRM_NOT_NULL_DEBUG(original);
    Util::Cast::Dynamic::test_throw_on_fail<Op::Eq, Util::Err::Type>(
        original->op, "Simplifer::eq's Expr's op must be an Op::Eq");
#endif
    Util::Log::verbose("Eq simplifier invoked");
    return original; // todo
}

/** @todo
 *  original may not be nullptr
 */
Expr::BasePtr Simplifier::ne(const Expr::BasePtr &original) {
    UTIL_AFFIRM_NOT_NULL_DEBUG(original);
    return original; // todo
}

/************************************************/
/*                   Boolean                    */
/************************************************/

/** @todo
 *  original may not be nullptr
 */
Expr::BasePtr Simplifier::Boolean::and_(const Expr::BasePtr &original) {
    UTIL_AFFIRM_NOT_NULL_DEBUG(original);
    return original; // todo
}

/** @todo
 *  original may not be nullptr
 */
Expr::BasePtr Simplifier::Boolean::or_(const Expr::BasePtr &original) {
    UTIL_AFFIRM_NOT_NULL_DEBUG(original);
    return original; // todo
}

/** @todo
 *  original may not be nullptr
 */
Expr::BasePtr Simplifier::Boolean::not_(const Expr::BasePtr &original) {
    UTIL_AFFIRM_NOT_NULL_DEBUG(original);
    return original; // todo
}

/************************************************/
/*                   Bitwise                    */
/************************************************/

/** @todo
 *  original may not be nullptr
 */
Expr::BasePtr Simplifier::Bitwise::add(const Expr::BasePtr &original) {
    UTIL_AFFIRM_NOT_NULL_DEBUG(original);
    return original; // todo
}

/** @todo
 *  original may not be nullptr
 */
Expr::BasePtr Simplifier::Bitwise::mul(const Expr::BasePtr &original) {
    UTIL_AFFIRM_NOT_NULL_DEBUG(original);
    return original; // todo
}

/** @todo
 *  original may not be nullptr
 */
Expr::BasePtr Simplifier::Bitwise::sub(const Expr::BasePtr &original) {
    UTIL_AFFIRM_NOT_NULL_DEBUG(original);
    return original; // todo
}

/** @todo
 *  original may not be nullptr
 */
Expr::BasePtr Simplifier::Bitwise::xor_minmax(const Expr::BasePtr &original) {
    UTIL_AFFIRM_NOT_NULL_DEBUG(original);
    return original; // todo
}

/** @todo
 *  original may not be nullptr
 */
Expr::BasePtr Simplifier::Bitwise::or_(const Expr::BasePtr &original) {
    UTIL_AFFIRM_NOT_NULL_DEBUG(original);
    return original; // todo
}

/** @todo
 *  original may not be nullptr
 */
Expr::BasePtr Simplifier::Bitwise::and_(const Expr::BasePtr &original) {
    UTIL_AFFIRM_NOT_NULL_DEBUG(original);
    return original; // todo
}

/** @todo
 *  original may not be nullptr
 */
Expr::BasePtr Simplifier::Bitwise::xor_(const Expr::BasePtr &original) {
    UTIL_AFFIRM_NOT_NULL_DEBUG(original);
    return original; // todo
}
