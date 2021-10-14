/**
 * @file
 * @brief This file defines PyObj::VS
 */
#ifndef R_PYOBJ_VS_HPP_
#define R_PYOBJ_VS_HPP_

#include "base.hpp"

#include "../bit_length.hpp"


namespace PyObj {

    /** A Value Set PyObj */
    struct VS final : public Base, public BitLength {

        /** Constructor */
        explicit inline VS(const Hash::Hash &h, const Ref r, const Constants::UInt bl) noexcept
            : Base { h, r }, BitLength { bl } {}
    };

    /** Define VS pointer alias */
    using VSPtr = std::shared_ptr<const VS>;

} // namespace PyObj

#endif
