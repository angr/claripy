/** @file */
#include "simplifiers.hpp"

#include "../op.hpp"


// For brevity
using SL = Simplify::SimplifyLog;


/** @todo
 *  original may not be nullptr
 */
static Expr::BasePtr if_(const Expr::BasePtr &original) {
    UTIL_ASSERT_NOT_NULL_DEBUG(original);
    return original;
}

/** @todo
 *  original may not be nullptr
 */
static Expr::BasePtr concat(const Expr::BasePtr &original) {
    UTIL_ASSERT_NOT_NULL_DEBUG(original);
    return original; // todo
}

namespace BV {
    /** @todo
     *  original may not be nullptr
     */
    static Expr::BasePtr reverse(const Expr::BasePtr &original) {
        UTIL_ASSERT_NOT_NULL_DEBUG(original);
        return original; // todo
    }
} // namespace BV

/************************************************/
/*                    Shift                     */
/************************************************/

namespace Shift {
    /** @todo
     *  original may not be nullptr
     */
    static Expr::BasePtr r(const Expr::BasePtr &original) {
        UTIL_ASSERT_NOT_NULL_DEBUG(original);
        return original; // todo
    }

    /** @todo
     *  original may not be nullptr
     */
    static Expr::BasePtr l(const Expr::BasePtr &original) {
        return original; // todo
    }

    /** @todo
     *  original may not be nullptr
     */
    static Expr::BasePtr lshr(const Expr::BasePtr &original) {
        return original; // todo
    }
} // namespace Shift

/************************************************/
/*                   Equality                   */
/************************************************/

/** @todo
 *  original may not be nullptr
 */
static Expr::BasePtr eq(const Expr::BasePtr &original) {
#ifdef DEBUG
    UTIL_ASSERT_NOT_NULL_DEBUG(original);
    Util::Cast::Dynamic::test_throw_on_fail<Op::Eq, Util::Err::Type>(
        original->op, "Simplifer::eq's Expr's op must be an Op::Eq");
#endif
    Util::Log::verbose<SL>("Eq simplifier invoked");
    return original; // todo
}

/** @todo
 *  original may not be nullptr
 */
static Expr::BasePtr ne(const Expr::BasePtr &original) {
    UTIL_ASSERT_NOT_NULL_DEBUG(original);
    return original; // todo
}

/************************************************/
/*                   Boolean                    */
/************************************************/

namespace Boolean {
    /** @todo
     *  original may not be nullptr
     */
    static Expr::BasePtr and_(const Expr::BasePtr &original) {
        UTIL_ASSERT_NOT_NULL_DEBUG(original);
        return original; // todo
    }

    /** @todo
     *  original may not be nullptr
     */
    static Expr::BasePtr or_(const Expr::BasePtr &original) {
        UTIL_ASSERT_NOT_NULL_DEBUG(original);
        return original; // todo
    }

    /** @todo
     *  original may not be nullptr
     */
    static Expr::BasePtr not_(const Expr::BasePtr &original) {
        UTIL_ASSERT_NOT_NULL_DEBUG(original);
        return original; // todo
    }
} // namespace Boolean

/************************************************/
/*                   Bitwise                    */
/************************************************/

namespace Bitwise {
    /** @todo
     *  original may not be nullptr
     */
    static Expr::BasePtr add(const Expr::BasePtr &original) {
        UTIL_ASSERT_NOT_NULL_DEBUG(original);
        return original; // todo
    }

    /** @todo
     *  original may not be nullptr
     */
    static Expr::BasePtr mul(const Expr::BasePtr &original) {
        UTIL_ASSERT_NOT_NULL_DEBUG(original);
        return original; // todo
    }

    /** @todo
     *  original may not be nullptr
     */
    static Expr::BasePtr sub(const Expr::BasePtr &original) {
        UTIL_ASSERT_NOT_NULL_DEBUG(original);
        return original; // todo
    }

    /** @todo
     *  original may not be nullptr
     */
    static Expr::BasePtr xor_minmax(const Expr::BasePtr &original) {
        UTIL_ASSERT_NOT_NULL_DEBUG(original);
        return original; // todo
    }

    /** @todo
     *  original may not be nullptr
     */
    static Expr::BasePtr or_(const Expr::BasePtr &original) {
        UTIL_ASSERT_NOT_NULL_DEBUG(original);
        return original; // todo
    }

    /** @todo
     *  original may not be nullptr
     */
    static Expr::BasePtr and_(const Expr::BasePtr &original) {
        UTIL_ASSERT_NOT_NULL_DEBUG(original);
        return original; // todo
    }

    /** @todo
     *  original may not be nullptr
     */
    static Expr::BasePtr xor_(const Expr::BasePtr &original) {
        UTIL_ASSERT_NOT_NULL_DEBUG(original);
        return original; // todo
    }
} // namespace Bitwise


// From header

/** A local macro for consistency */
#define ENTRY(X, ...)                                                                              \
    {                                                                                              \
        (::Op::X::static_cuid), { __VA_ARGS__ }                                                    \
    }

Simplify::Vec Simplify::builtin_vec() {
    return {};
}

Simplify::Map Simplify::builtin_map() {
    // @todo: Remove sink
    Util::sink(concat, BV::reverse, Shift::r, Shift::l, Shift::lshr, eq, ne, Boolean::and_,
               Boolean::or_, Boolean::not_, Bitwise::add, Bitwise::mul, Bitwise::sub,
               Bitwise::xor_minmax, Bitwise::or_, Bitwise::and_, Bitwise::xor_);
    return {
        ENTRY(If, if_),
    };
}

// Cleanup
#undef ENTRY