/**
 * @file
 * @brief This file defines the base expression
 */
#ifndef R_EXPRESSION_BASE_HPP_
#define R_EXPRESSION_BASE_HPP_

#include "../annotation.hpp"
#include "../factory.hpp"

#include <memory>
#include <sstream>
#include <vector>


namespace Op {
    class Base;
    using BasePtr = Factory::Ptr<Base>;
} // namespace Op

namespace Expression {

    /** The base Expression type
     *  All expressions must subclass this
     */
    class Base : public Factory::FactoryMade {
        FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(Base, 0)
      public:
        /** Annotation vector type */
        using AnVec = std::vector<Annotation::BasePtr>;

        /** A set of annotations applied onto this Expression */
        const AnVec annotations;

        /** Return true if and only if this expression is symbolic */
        const bool symbolic;

        /** The Expression Op */
        const Op::BasePtr op;

      protected:
        /** Protected Constructor */
        explicit inline Base(const Hash::Hash h, const CUID::CUID &c, AnVec &&ans, const bool sym,
                             Op::BasePtr &&op_) noexcept
            : FactoryMade { h, c }, annotations { std::move(ans) }, symbolic { sym }, op { op_ } {
#ifdef DEBUG
            ctor_debug_checks();
#endif
        }

        /** Pure virtual destructor */
        inline ~Base() noexcept override = 0;

      private:
        /** Used during debugging for extra checks
         *  These need access to the internals of op so the cannot be inlined
         */
        void ctor_debug_checks() const;

        // Disable other methods of construction
        SET_IMPLICITS_CONST_MEMBERS(Base, delete)
    };

    /** An alias for Factory::Ptr<Expression::Base> */
    using RawPtr = Constants::CTS<Base>;

    /** An alias for Factory::Ptr<Expression::Base> */
    using BasePtr = Factory::Ptr<Base>;

    /** Default virtual destructor */
    Base::~Base() noexcept = default;

} // namespace Expression

#endif
