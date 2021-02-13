/**
 * @file
 * @brief A unary Op
 */
#ifndef __OP_UNARY_HPP__
#define __OP_UNARY_HPP__

#include "base.hpp"

#include "../error.hpp"

#include <memory>


/** A macro used to define a trivial subclass of Unary
 *  Pass template arguments to Unary via variadic macro arguments
 */
#define OP_UNARY_TRIVIAL_SUBCLASS(CLASS)                                                          \
    class CLASS final : public ::Op::Unary {                                                      \
        OP_FINAL_INIT(CLASS)                                                                      \
      private:                                                                                    \
        /** Private constructor */                                                                \
        explicit inline CLASS(const ::Hash::Hash &h, const ::Expression::BasePtr &x)              \
            : Unary { h, static_cuid, x } {}                                                      \
    };


namespace Op {

    /** A Unary Op class */
    class Unary : public Base {
        OP_PURE_INIT(Unary)
      public:
        /** The operand */
        const Expression::BasePtr child;

      protected:
        /** Protected constructor */
        explicit inline Unary(const Hash::Hash &h, const CUID::CUID &cuid_,
                              const Expression::BasePtr &x)
            : Base { h, cuid_ }, child { x } {}
    };

    /** Default virtual destructor */
    Unary::~Unary() noexcept = default;

    /** Returns true if T is unary */
    template <typename T> UTILS_ICCBOOL is_unary { Utils::is_ancestor<Unary, T> };

} // namespace Op

#endif
