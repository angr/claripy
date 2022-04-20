/**
 * @file
 * @brief This file defines PyObj
 */
#ifndef R_SRC_PYOBJ_BASE_HPP_
#define R_SRC_PYOBJ_BASE_HPP_

#include "../hash.hpp"
#include "../macros.hpp"

#include <memory>


namespace PyObj {

    /** A class containing a ref to some python object and a hash */
    struct Base : public Hash::Hashed {
        /** The python reference type PyObj uses */
        using Ref = U64;

        /** Constructor */
        explicit inline Base(const Hash::Hash &h, const Ref r) noexcept : Hashed { h }, ref { r } {}
        // Default implicits
        DEFINE_IMPLICITS_CONST_MEMBERS_ALL_NOEXCEPT(Base);

        /** The reference to the python object */
        const Ref ref;
    };

    namespace Private {
        /** If not DEBUG, returns ret; else if ret and not cond report user error detected */
        inline bool eq(const bool ret, const bool cond) {
#ifdef DEBUG
            UTIL_ASSERT(Util::Err::HashCollision, ret && !cond,
                        "PyObjects equate but are different; this is probably due to user error");
#else
            (void) cond;
#endif
            return ret;
        }
    } // namespace Private

    /** Equality operator */
    inline bool operator==(const Base &a, const Base &b) {
        return Private::eq(a.hash == b.hash, a.ref == b.ref);
    }
    /** Anti-equality operator */
    inline bool operator!=(const Base &a, const Base &b) {
        return !(a == b);
    }

} // namespace PyObj

#endif
