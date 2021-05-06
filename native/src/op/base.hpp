/**
 * @file
 * @brief This file defines the base op class
 */
#ifndef __OP_BASE_HPP__
#define __OP_BASE_HPP__

#include "macros.hpp"

#include "../expression.hpp" // For subclasses
#include "../factory.hpp"

#include <stack>


namespace Op {

    /** Base operation expression
     *  All op expressions must subclass this
     */
    class Base : public Factory::FactoryMade {
        OP_PURE_INIT(Base);

      public:
        /** The type of the stack usd in the add_reversed_children function */
        using Stack = std::stack<Expression::RawPtr, std::vector<Expression::RawPtr>>;
        /** The name of the op */
        virtual inline Constants::CCS op_name() const noexcept = 0;
        /** Python's repr function (outputs json) */
        virtual inline void repr(std::ostringstream &out, const bool verbose = false) const = 0;
        /** Add's the raw expression children of the expression to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        virtual inline void add_reversed_children(Stack &) const = 0;

      protected:
        /** Protected constructor */
        explicit inline Base(const Hash::Hash &h, const CUID::CUID &cuid_) noexcept
            : FactoryMade { h, cuid_ } {}
    };

    /** An alias for Factory::Ptr<Base> */
    using BasePtr = Factory::Ptr<Base>;

    /** Default virtual destructor */
    Base::~Base() noexcept = default;

} // namespace Op


#endif
