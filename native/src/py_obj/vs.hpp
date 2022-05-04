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
        /** Shared pointer to a const VS */
        using Ptr = std::shared_ptr<const VS>;
        /** A constructor for VS objects
         *  Note: we don't template so that bindings can easily be made
         */
        static inline Ptr factory(const Hash::Hash &h, const Ref r, const U64 bl) {
            return Ptr { new VS { h, r, bl } };
        }

      private:
        /** Constructor */
        explicit inline VS(const Hash::Hash &h, const Ref r, const U64 bl) noexcept
            : Base { h, r }, BitLength { bl } {}
    };

    /** Equality operator */
    inline bool operator==(const VS &a, const VS &b) {
        return Private::eq(static_cast<const Base &>(a) == b, a.bit_length == b.bit_length);
    }

    /** Stream operator */
    inline std::ostream &operator<<(std::ostream &os, const VS &vs) {
        return os << "VS{hash = " << vs.hash << ", ref = " << vs.ref
                  << ", bit_length = " << vs.bit_length << "}";
    }

} // namespace PyObj

#endif
