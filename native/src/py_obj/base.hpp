/**
 * @file
 * @brief This file defines PyObj
 */
#ifndef __PYOBJ_BASE_HPP__
#define __PYOBJ_BASE_HPP__

#include "../hash.hpp"
#include "../macros.hpp"

#include <memory>


namespace PyObj {

    /** A class containing a ref to some python object and a hash */
    struct Base : Hash::Hashed {

        /** Constructor */
        explicit inline Base(const Hash::Hash &h, Constants::UInt r) noexcept
            : Hashed { h }, ref { r } {}

        /** Pure virtual destructor */
        inline virtual ~Base() noexcept = 0;

        // Default implicits
        SET_IMPLICITS_CONST_MEMBERS(Base, default, noexcept);

        /** The reference to the python object */
        const Constants::UInt ref;
    };

    /** Default destructor */
    Base::~Base() noexcept = default;

    /** Define base pointer alias */
    using BasePtr = std::shared_ptr<const Base>;
} // namespace PyObj

#endif
