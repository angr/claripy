/**
 * @file
 * @brief This file defines PyObj::VS
 */
#ifndef R_SRC_PYOBJ_VS_HPP_
#define R_SRC_PYOBJ_VS_HPP_

#include "base.hpp"

#include "../bit_length.hpp"


namespace PyObj {

    /** A Value Set PyObj */
    struct VS final : public Base, public BitLength {
        CUID_DEFINE_MAYBE_UNUSED
        /** Shared pointer to a const VS */
        using Ptr = std::shared_ptr<const VS>;
        /** A constructor for VS objects
         *  Note: we don't template so that bindings can easily be made
         */
        static inline Ptr factory(const Hash::Hash &h, const U64 bl) {
            return Ptr { new VS { h, bl } };
        }

      private:
        /** Constructor */
        explicit inline VS(const Hash::Hash &h, const U64 bl) noexcept
            : Base { h }, BitLength { bl } {}
    };

    /** Equality operator */
    inline bool operator==(const VS &a, const VS &b) {
        const bool ret { a.hash == b.hash };
#ifdef DEBUG
        UTIL_ASSERT(Util::Err::HashCollision, ret == (a.bit_length == b.bit_length),
                    "PyObjects equate but are different; this is probably due to user error");
#endif
        return ret;
    }
    /** Not-equality operator */
    inline bool operator!=(const VS &a, const VS &b) {
        return not(a == b);
    }

    /** Stream operator */
    inline std::ostream &operator<<(std::ostream &os, const VS &vs) {
        return os << "VS{hash = " << vs.hash << ", bit_length = " << vs.bit_length << "}";
    }

} // namespace PyObj

#endif
