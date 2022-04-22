/**
 * @file
 * @brief This file defines Expr factory functions
 */
#ifndef R_SRC_EXPR_FACTORY_HPP_
#define R_SRC_EXPR_FACTORY_HPP_

#include "base.hpp"
#include "instantiables.hpp"

#include "../hash.hpp"
#include "../util.hpp"


namespace Expr {

    /** A factory used to construct Expr::Base subclasses
     *  Arguments are passed by non-const forwarding reference
     *  @todo update eager_backends functionality
     */
    template <typename T, typename... Args> BasePtr factory(Args &&...args) {
        static_assert(Util::Type::Is::ancestor<Base, T>, "T must derive from Expr::Base");
        return ::Factory::factory<Base, T>(std::forward<Args>(args)...);
    }

    /** A factory used to construct Expr::Bits subclasses
     *  Arguments are passed by non-const forwarding reference
     *  The type is determined by cuid; supported types: subclasses of Bits
     *  Note: Bools are not supported as variatic args would not work here as it would required
     *  Bools to have a constructor that takes in the same types as String; including bit_length
     *  Likewise, the subclasses of Bits are all supported *only* because each of their
     *  constructors take in the same arguments. This is because this is dynamic dispatch so each
     *  type must have a constructor which takes in the same arguments as the compiler can't prove
     *  you won't need to call it; i.e. in the case the code has bugs or something.
     */
    template <typename... Args> BasePtr factory_cuid(const CUID::CUID cuid, Args &&...args) {
#define M_CASE(T)                                                                                  \
    case T::static_cuid: /* This static_assert is why we disallow Bools */                         \
        static_assert(Util::Type::Has::constructor<T, Hash::Hash, Args...>,                        \
                      "Cannot construct " #T);                                                     \
        return ::Expr::factory<T, Args...>(std::forward<Args>(args)...)
        switch (cuid) {
            M_CASE(String);
            M_CASE(FP);
            M_CASE(VS);
            M_CASE(BV);
            case Bool::static_cuid:
                UTIL_THROW(Util::Err::Usage,
                           "Cannot construct a Bool; use factory<Expr::Bool instead");
            default:
                UTIL_THROW(Util::Err::Usage, "Unknown cuid: ", cuid);
#undef M_CASE
        }
    }

    /** Get a shared pointer from a hash
     *  If the object does not exist it returns a shared pointer to nullptr
     */
    inline Factory::Ptr<Base> find(const Hash::Hash h) {
        return ::Factory::find<Base>(h);
    }

} // namespace Expr

#endif
