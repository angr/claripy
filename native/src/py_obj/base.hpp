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

    /** A class containing a ref to some python object and a hash
     *  Warning: No virtual destructor; do *not* delete by base class pointer; avoid slicing!
     */
    struct Base : public Hash::Hashed {
      protected:
        /** Inherit constructor */
        using Hashed::Hashed;
        /** Protected destructor to prevent most slicing */
        inline ~Base() noexcept = default;
        // Rule of 5
        DEFINE_IMPLICITS_CONST_MEMBERS_ALL_NOEXCEPT(Base);
    };

} // namespace PyObj

#endif
