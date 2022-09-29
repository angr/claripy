/**
 * @file
 * @brief This file defines the base expr
 */
#ifndef R_SRC_EXPR_BASE_HPP_
#define R_SRC_EXPR_BASE_HPP_

#include "../error.hpp"
#include "../factory.hpp"
#include "../has_repr.hpp"

#include <memory>
#include <sstream>
#include <vector>


// Forward declarations
namespace Op {
    class Base;
    using BasePtr = Factory::Ptr<const Base>;
} // namespace Op

namespace Expr {

    /** An optional python dict type
     *  TODO: this should probably be a subclass of Hashed and pybind11::dict somehow
     */
    using OpPyDict = std::optional<pybind11::dict>;

    /** The base Expr type
     *  All Exprs must subclass this
     *  Annotations passed via the python dict *must* be stored in a tuple
     */
    class Base : public HasRepr<Base>, public Factory::FactoryMade {
        FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(Base)
      public:
        /** Return true if and only if this expr is symbolic */
        const bool symbolic;
        /** The Expr Op */
        const Op::BasePtr op;
        /** A set of annotations applied onto this Expr
         *  Warning: This dict should never be edited
         *  pybind11 doesn't really do const, so we can't here either :(
         */
        const OpPyDict dict;

        // Functions

        /** Get the type name */
        virtual inline const char *type_name() const noexcept = 0;
        /** Get the Expr's repr */
        void repr_stream(std::ostream &out) const;
        /** Get annotations
         *  Warning: Do not edit this dict
         *  pybind11 doesn't really do const, so we can't here either :(
         */
        inline std::optional<pybind11::tuple> annotations() const {
            if (dict) {
                const auto &d { dict.value() };
                if (d.contains(ANNOTATIONS_KEY)) {
                    return d[ANNOTATIONS_KEY];
                }
            }
            return {};
        }

      protected:
        /** Protected Constructor */
        explicit inline Base(const Hash::Hash h, const CUID::CUID c, const bool sym,
                             Op::BasePtr &&o, OpPyDict &&d) NOEXCEPT_UNLESS_DEBUG :
            FactoryMade { h, c },
            symbolic { sym },
            op { std::move(o) },
            dict { std::move(d) } {
#ifdef DEBUG
            if (dict && dict->contains(ANNOTATIONS_KEY)) {
                UTIL_ASSERT(Error::Expr::Type, PyTuple_Check(dict.value()[ANNOTATIONS_KEY].ptr()),
                            "Annotations must be passed as a tuple");
            }
            UTIL_ASSERT(Util::Err::Usage, op, "op may not be nullptr");
            ctor_debug_checks();
#endif
        }

        /** Pure virtual destructor */
        virtual inline ~Base() noexcept = 0;

      private:
        /** Used during debugging for extra checks
         *  These need access to the internals of op so it cannot be inlined
         */
        void ctor_debug_checks() const;

        // Disable other methods of construction
        SET_IMPLICITS_CONST_MEMBERS(Base, delete)
    };

    /** An alias for Factory::Ptr<const Expr::Base> */
    using RawPtr = const Base *;

    /** An alias for Factory::Ptr<const Expr::Base> */
    using BasePtr = Factory::Ptr<const Base>;

    /** Default virtual destructor */
    Base::~Base() noexcept = default;

    /** Overload the << stream operator to use repr */
    inline std::ostream &operator<<(std::ostream &os, const RawPtr &p) {
        if (UNLIKELY(p == nullptr)) {
            os << "(null Expr::BasePtr)";
        }
        else {
            p->repr_stream(os);
        }
        return os;
    }

    /** Overload the << stream operator to use repr */
    inline std::ostream &operator<<(std::ostream &os, const BasePtr &p) {
        return (os << p.get());
    }

} // namespace Expr

#endif
