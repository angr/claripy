/**
 * @file
 * @brief This file defines PyObj
 */
#ifndef R_SRC_PYOBJ_BASE_HPP_
#define R_SRC_PYOBJ_BASE_HPP_

#include "../bit_length.hpp"
#include "../has_repr.hpp"
#include "../hash.hpp"
#include "../macros.hpp"

#include <memory>


namespace PyObj {

    /** A class containing a ref to some python object and a hash
     *  Warning: No virtual destructor; do *not* delete by base class pointer; avoid slicing!
     */
    class Base : public Hash::Hashed, public HasRepr<Base> {
      public:
        /** Override repr stream */
        virtual inline void repr_stream(std::ostream &o) const final { o << actual_repr(); }

      protected:
        /** Inherit constructor */
        using Hashed::Hashed;
        /** Protected destructor to prevent most slicing */
        inline ~Base() noexcept = default;
        // Rule of 5
        DEFINE_IMPLICITS_CONST_MEMBERS_ALL_NOEXCEPT(Base);
        /** Call repr on the python object */
        virtual std::string actual_repr() const = 0;
    };

    /** A sized python object
     *  Warning: No virtual destructor; do *not* delete by base class pointer; avoid slicing!
     */
    class Sized : public Base, public BitLength {
      protected:
        /** Constructor */
        explicit constexpr Sized(const Hash::Hash h, const U64 bl) noexcept
            : Base { h }, BitLength { bl } {}
        /** Protected destructor to prevent most slicing */
        inline ~Sized() noexcept = default;
        // Rule of 5
        DEFINE_IMPLICITS_CONST_MEMBERS_ALL_NOEXCEPT(Sized);
    };

} // namespace PyObj

#endif
