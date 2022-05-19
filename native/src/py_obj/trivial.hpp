/**
 * @file
 * @brief This file defines trivial PyObjs
 */
#ifndef R_SRC_PYOBJ_TRIVIAL_HPP_
#define R_SRC_PYOBJ_TRIVIAL_HPP_

#include "base.hpp"

#include "../bit_length.hpp"


// Macros


#define M_NEW_PYOBJ_CLS(NAME)                                                                      \
    struct NAME final : public Base, public BitLength {                                            \
        CUID_DEFINE_MAYBE_UNUSED                                                                   \
        /** Shared pointer to a const *this */                                                     \
        using Ptr = std::shared_ptr<const NAME>;                                                   \
        /** A non-templated public constructor (can be bound by API) */                            \
        static inline Ptr factory(const Hash::Hash &h, const U64 bl) {                             \
            return Ptr { new NAME { h, bl } };                                                     \
        }                                                                                          \
                                                                                                   \
      private:                                                                                     \
        /** Constructor */                                                                         \
        explicit constexpr NAME(const Hash::Hash &h, const U64 bl) noexcept                        \
            : Base { h }, BitLength { bl } {}                                                      \
    };

#define M_NEW_PYOBJ_FUNCS(NAME)                                                                    \
    /** Equality operator */                                                                       \
    constexpr bool operator==(const NAME &a, const NAME &b) {                                      \
        return a.hash == b.hash;                                                                   \
    };                                                                                             \
    /** Not-equality operator */                                                                   \
    constexpr bool operator!=(const NAME &a, const NAME &b) {                                      \
        return not(a == b);                                                                        \
    }                                                                                              \
    /** Stream operator */                                                                         \
    inline std::ostream &operator<<(std::ostream &os, const NAME &obj) {                           \
        return os << #NAME "{hash = " << obj.hash << ", bit_length = " << obj.bit_length << "}";   \
    }

#define M_NEW_PYOBJ(NAME)                                                                          \
    M_NEW_PYOBJ_CLS(NAME);                                                                         \
    M_NEW_PYOBJ_FUNCS(NAME)


// Non-macros


namespace PyObj {
    /** A Value Set PyObj */
    M_NEW_PYOBJ(VS);
    /** A BV Arg PyObj */
    M_NEW_PYOBJ(BVArg);
} // namespace PyObj


#undef M_NEW_PYOBJ
#undef M_NEW_PYOBJ_CLS
#undef M_NEW_PYOBJ_FUNCS

#endif
