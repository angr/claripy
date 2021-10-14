/**
 * @file
 * @brief This file defines PyObj
 */
#ifndef R_PYOBJ_BASE_HPP_
#define R_PYOBJ_BASE_HPP_

#include "../hash.hpp"
#include "../macros.hpp"

#include <memory>


namespace PyObj {

    /** A class containing a ref to some python object and a hash */
    struct Base : public Hash::Hashed {
        /** The python reference type PyObj uses */
        using Ref = Constants::UInt;

        /** Constructor */
        explicit inline Base(const Hash::Hash &h, const Ref r) noexcept
            : Hashed { h }, ref { r } {}

        /** Pure virtual destructor */
        virtual inline ~Base() noexcept = 0;

        // Default implicits
        DEFINE_IMPLICITS_CONST_MEMBERS_ALL_NOEXCEPT(Base);

        /** The reference to the python object */
        const Ref ref;
    };

    /** Default destructor */
    Base::~Base() noexcept = default;

    /** Define base pointer alias */
    using BasePtr = std::shared_ptr<const Base>;

} // namespace PyObj

#endif
