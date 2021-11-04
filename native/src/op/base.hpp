/**
 * @file
 * @brief This file defines the base op class
 */
#ifndef R_OP_BASE_HPP_
#define R_OP_BASE_HPP_

#include "macros.hpp"

#include "../expr.hpp" // For subclasses
#include "../factory.hpp"

#include <stack>


namespace Op {

    /** Base operation expr
     *  All op exprs must subclass this
     */
    class Base : public Factory::FactoryMade {
        OP_PURE_INIT(Base);

      public:
        /** The type of the stack usd in the unsafe_add_reversed_children function */
        using Stack = std::stack<Expr::RawPtr, std::vector<Expr::RawPtr>>;
        /** A variant containing every type an op can hold */
        using ArgVar = std::variant<Expr::BasePtr>;

        /** The name of the op */
        virtual inline const char *op_name() const noexcept = 0;
        /** Python's repr function (outputs json) */
        virtual inline void repr(std::ostream &out, const bool verbose = false) const = 0;

        /** Adds the raw expr children of the expr to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        virtual inline void unsafe_add_reversed_children(Stack &) const = 0;
        /** Appends the expr children of the expr to the given vector
         *  Note: This should only be used when returning children to python
         */
        //        virtual inline void python_children(std::vector<ArgVar> &) const = 0; @todo

      protected:
        /** Protected constructor */
        explicit inline Base(const Hash::Hash &h, const CUID::CUID &cuid_) noexcept
            : FactoryMade { h, cuid_ } {}
    };

    /** An alias for Factory::Ptr<const Op::Base> */
    using BasePtr = Factory::Ptr<const Base>;

    /** Default virtual destructor */
    Base::~Base() noexcept = default;

} // namespace Op


#endif
