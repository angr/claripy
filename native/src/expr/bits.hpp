/**
 * @file
 * @brief This file defines the Bits class
 */
#ifndef R_SRC_EXPR_BITS_HPP_
#define R_SRC_EXPR_BITS_HPP_

#include "base.hpp"

#include "../bit_length.hpp"


namespace Expr {

    /** This class represents an Expr of Bits */
    class Bits : public Base, public BitLength {
        FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(Base)
      protected:
        /** Protected Constructor */
        explicit inline Bits(const Hash::Hash h, const CUID::CUID &c, const bool sym,
                             Op::BasePtr &&o, OpPyDict &&d, const U64 bit_length) noexcept
            : Base { h, c, sym, std::move(o), std::move(d) }, BitLength { bit_length } {}


        /** Pure virtual destructor */
        inline ~Bits() noexcept override = 0;

      private:
        // Disable other methods of construction
        SET_IMPLICITS_CONST_MEMBERS(Bits, delete)
    };

    /** Default virtual destructor */
    Bits::~Bits() noexcept = default;

    /** Static casts T to Expr::Bits' raw pointer, then returns the bit_length
     *  p may not be nullptr
     *  Warning: This static casts, the user must ensure that p is a Bits
     */
    constexpr U64 bit_length(const Expr::RawPtr p) {
        UTIL_ASSERT_NOT_NULL_DEBUG(p);
        using To = const Expr::Bits *;
        return Util::checked_static_cast<To>(p)->bit_length;
    }

    /** Static casts T to Expr::Bits, then returns the bit_length
     *  p may not be nullptr
     *  Warning: This static casts, the user must ensure that p.get() is a Bits
     */
    inline U64 bit_length(const Expr::BasePtr &p) {
        UTIL_ASSERT_NOT_NULL_DEBUG(p);
        return bit_length(p.get());
    }

} // namespace Expr

#endif
