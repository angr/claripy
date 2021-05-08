/**
 * @file
 * @brief This file defines PyObj
 */
#ifndef __PYOBJ_TRIVIAL_HPP__
#define __PYOBJ_TRIVIAL_HPP__

#include "base.hpp"


namespace PyObj {

    /** VS pointer */
    struct VS final : public Base {
        SET_IMPLICITS_CONST_MEMBERS(VS, default, noexcept);
        /** Destructor */
        inline ~VS() override final = default;
    };

    /** Define VS pointer alias */
    using VSPtr = std::shared_ptr<const VS>;
} // namespace PyObj

#endif
