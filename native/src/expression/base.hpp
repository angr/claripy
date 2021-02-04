/**
 * @file
 * @brief This file defines the base expression
 */
#ifndef __EXPRESSION_BASE_HPP__
#define __EXPRESSION_BASE_HPP__

#include "macros.hpp"

#include "../factory.hpp"
#include "../op.hpp"

#include <memory>
#include <vector>


// Forward declarations
namespace Annotation {
    struct Base;
}

namespace Expression {

    /** The base Expression type
     *  All expressions must subclass this
     */
    class Base : public Factory::FactoryMade {
        FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(Base)
      public:
        /** Return true if and only if this expression is symbolic */
        const bool symbolic;

        /** The Expression Op */
        const Factory::Ptr<Op::Base> op;

        /** A set of annotations applied onto this Expression */
        const std::vector<Factory::Ptr<Annotation::Base>> annotations;

      protected:
/** We make this a macro for brevity in subclasses */
#define EXPRESSION_BASE_ARGS(HASH, CUID, SYM, OP, ANS)                                            \
    const Hash::hash HASH, const Constants::UInt CUID const bool SYM Factory::Ptr<Op::Base> &&OP, \
        std::vector<Factory::Ptr<Annotation::Base>> &&ANS

        /** Protected Constructor */
        explicit inline Base(EXPRESSION_BASE_ARGS(h, c, sym, op_, annotations_)) noexcept
            : FactoryMade { h, c }, symbolic { sym }, op { op_ }, annotations { annotations_ } {
#ifdef DEBUG
            if (const auto cast { std::dynamic_pointer_cast<CSized>(op_) }; cast) {
                using Err = Utils::Error::Unexpected::Base;
                Utils::affirm<Err>(op_.size == this->size,
                                   "CSized Op size and Bits size mismatch");
            }
#endif
        }

        /** Pure virtual destructor */
        inline ~Base() noexcept override = 0;

        // Disable other methods of construction
        SET_IMPLICITS_CONST_MEMBERS(Base, delete)
    };

    /** Default virtual destructor */
    Base::~Base() noexcept = default;

} // namespace Expression

#endif
