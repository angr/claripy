/**
 * @file
 * @brief This file defines the base op class
 */
#ifndef R_SRC_OP_BASE_HPP_
#define R_SRC_OP_BASE_HPP_

#include "constants.hpp"
#include "macros.hpp"

#include "../factory.hpp"
#include "../has_repr.hpp"


namespace Op {

    /** Base operation expr
     *  All op exprs must subclass this
     */
    class Base : public HasRepr, public Factory::FactoryMade {
        OP_PURE_INIT(Base);

      public:
        /** The name of the op */
        virtual inline const char *op_name() const noexcept = 0;

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

    /** Overload the << stream operator to use repr */
    inline std::ostream &operator<<(std::ostream &os, const Op::Base *p) {
        if (UNLIKELY(p == nullptr)) {
            os << "(null Op::BasePtr)";
        }
        else {
            p->repr_stream(os);
        }
        return os;
    }

    /** Overload the << stream operator to use repr */
    inline std::ostream &operator<<(std::ostream &os, const BasePtr &p) {
        os << p.get();
        return os;
    }

} // namespace Op


#endif
