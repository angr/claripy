/**
 * @file
 * @brief This file defines PyObj
 */
#ifndef __PYOBJ_TRIVIAL_HPP__
#define __PYOBJ_TRIVIAL_HPP__

#include "base.hpp"


namespace PyObj {

    /** VS pointer */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(VS, Base);

    /** Define VS pointer alias */
    using VSPtr = std::shared_ptr<const VS>;

} // namespace PyObj

#endif
