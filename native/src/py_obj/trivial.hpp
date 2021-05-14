/**
 * @file
 * @brief This file defines PyObj
 */
#ifndef R_PYOBJ_TRIVIAL_HPP_
#define R_PYOBJ_TRIVIAL_HPP_

#include "base.hpp"


namespace PyObj {

    /** VS pointer */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(VS, Base);

    /** Define VS pointer alias */
    using VSPtr = std::shared_ptr<const VS>;

} // namespace PyObj

#endif
