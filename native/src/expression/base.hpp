/**
 * @file
 * @brief This file defines the base expression
 */
#ifndef __EXPRESSION_BASE_HPP__
#define __EXPRESSION_BASE_HPP__

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

        /** Annotation vector type */
        using AnnotationVec = std::vector<Factory::Ptr<Annotation::Base>>;

        /** A set of annotations applied onto this Expression */
        const AnnotationVec annotations;

      protected:
        /** Protected Constructor */
        explicit inline Base(const Hash::Hash h, const CUID::CUID &c, const bool sym,
                             Factory::Ptr<Op::Base> &&op_, AnnotationVec &&annotations_) noexcept
            : FactoryMade { h, c }, symbolic { sym }, op { op_ }, annotations { annotations_ } {
#ifdef DEBUG
            if (const auto cast { Utils::dynamic_down_cast<Op::Symbol>(op_) }; cast) {
                using Err = Utils::Error::Unexpected::IncorrectUsage;
                Utils::affirm<Err>(symbolic, "Symbolic Op may not be concrete");
            }
            else if (const auto cast2 { Utils::dynamic_down_cast<Op::Literal>(op_) }; cast2) {
                using Err = Utils::Error::Unexpected::IncorrectUsage;
                Utils::affirm<Err>(!symbolic, "Literal Op may not be symbolic");
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
