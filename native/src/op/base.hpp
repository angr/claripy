/**
 * @file
 * @brief This file defines the base op class
 */
#ifndef R_OP_BASE_HPP_
#define R_OP_BASE_HPP_

#include "constants.hpp"
#include "macros.hpp"

#include "../factory.hpp"


namespace Op {

    /** Base operation expr
     *  All op exprs must subclass this
     */
    class Base : public Factory::FactoryMade {
        OP_PURE_INIT(Base);

      public:
        /** The name of the op */
        virtual inline const char *op_name() const noexcept = 0;
        /** Python's repr function, but appends to an ostream (outputs json) */
        virtual inline void append_repr(std::ostream &out) const = 0;
        /** Python's repr function (outputs json) */
        inline std::string repr() const {
            std::ostringstream s;
            append_repr(s);
            return s.str();
        }

        /** Adds the raw expr children of the expr to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         *  Be careful to ensure 'this' does not destruct while using said pointers
         */
        virtual inline void unsafe_add_reversed_children(Stack &) const = 0;
        /** Appends the expr children of the expr to the given vector
         *  Note: This should only be used when returning children to python
         */
        virtual inline std::vector<ArgVar> python_children() const = 0;

      protected:
        /** Protected constructor */
        explicit inline Base(const Hash::Hash &h, const CUID::CUID &cuid_) noexcept
            : FactoryMade { h, cuid_ } {}
    };

    /** An alias for Factory::Ptr<const Op::Base> */
    using BasePtr = Factory::Ptr<const Base>;

    /** Default virtual destructor */
    inline Base::~Base() noexcept = default;

} // namespace Op


#endif
