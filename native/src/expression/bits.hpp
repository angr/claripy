/**
 * @file
 * @brief This file defines the Bits class
 */
#ifndef __EXPRESSION_BITS_HPP__
#define __EXPRESSION_BITS_HPP__

#include "base.hpp"

#include "../csized.hpp"


namespace Expression {

    /** This class represents an Expression of Bits */
    class Bits : public Base, public CSized {
        FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(Base)
      protected:
        /** Protected Constructor */
        explicit inline Bits(const Hash::Hash h, const CUID::CUID &c, AnVec &&ans, const bool sym,
                             Op::BasePtr &&op_, const Constants::UInt size_) noexcept
            : Base { h, c, std::forward<AnVec>(ans), sym, std::forward<Op::BasePtr>(op_) },
              CSized { size_ } {}

        /** Pure virtual destructor */
        inline ~Bits() noexcept override = 0;

      private:
        // Disable other methods of construction
        SET_IMPLICITS_CONST_MEMBERS(Bits, delete)
    };

    /** Default virtual destructor */
    Bits::~Bits() noexcept = default;

} // namespace Expression

#endif
