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
        explicit inline Bits(const Hash::Hash h, const CUID::CUID &c, const bool sym,
                             Factory::Ptr<Op::Base> &&op_, AnnotationVec &&annotations_,
                             const Constants::UInt size_) noexcept
            : Base { h, c, sym, std::forward<Factory::Ptr<Op::Base>>(op_),
                     std::forward<AnnotationVec>(annotations_) },
              CSized { size_ } {
#ifdef DEBUG
            if (const auto cast { Utils::dynamic_pointer_cast<CSized>(op_) }; cast) {
                using Err = Utils::Error::Unexpected::Base;
                Utils::affirm<Err>(cast->size == this->size,
                                   "CSized Op size and Bits size mismatch");
            }
#endif
        }

        /** Pure virtual destructor */
        inline ~Bits() noexcept override = 0;

        // Disable other methods of construction
        SET_IMPLICITS_CONST_MEMBERS(Bits, delete)
    };

    /** Default virtual destructor */
    Bits::~Bits() noexcept = default;

} // namespace Expression

#endif
