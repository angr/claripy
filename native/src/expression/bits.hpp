/**
 * @file
 * @brief This file defines the Bits class
 */
#ifndef R_EXPRESSION_BITS_HPP_
#define R_EXPRESSION_BITS_HPP_

#include "base.hpp"

#include "../bit_length.hpp"


namespace Expression {

    /** This class represents an Expression of Bits */
    class Bits : public Base, public BitLength {
        FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(Base, 0)
      protected:
        /** Protected Constructor */
        explicit inline Bits(const Hash::Hash h, const CUID::CUID &c, AnVec &&ans, const bool sym,
                             Op::BasePtr &&op_, const Constants::UInt bit_length_) noexcept
            : Base { h, c, std::forward<AnVec>(ans), sym, std::forward<Op::BasePtr>(op_) },
              BitLength { bit_length_ } {}

        /** Pure virtual destructor */
        inline ~Bits() noexcept override = 0;

      private:
        // Disable other methods of construction
        SET_IMPLICITS_CONST_MEMBERS(Bits, delete)
    };

    /** Default virtual destructor */
    Bits::~Bits() noexcept = default;

    /** Static casts T to Expression::Bits' raw pointer, then returns the bit_length
     *  Warning: This static casts, the user must ensure that p is a Bits
     */
    constexpr Constants::UInt get_bit_length(const Expression::RawPtr &p) {
        using To = Constants::CTS<Expression::Bits>;
        return Utils::checked_static_cast<To>(p)->bit_length;
    }

    /** Static casts T to Expression::Bits, then returns the bit_length
     *  Warning: This static casts, the user must ensure that p.get() is a Bits
     */
    inline Constants::UInt get_bit_length(const Expression::BasePtr &p) {
        return get_bit_length(p.get());
    }

} // namespace Expression

#endif
