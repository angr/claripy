/**
 * @file
 * @brief A unary Op
 */
#ifndef __OP_UNARY_HPP__
#define __OP_UNARY_HPP__

#include "base.hpp"

#include "../error.hpp"


/** A macro used to define a trivial subclass of Unary
 *  Pass template arguments to Unary via variadic macro arguments
 *  An additional argument can be passed as the prefix to the desired debug name of the class
 *  For example, "FP::" may be desired for an FP op
 *  X can be anything, but must be different between different templates of the same class
 *  For example, Foo<int> must give a different X from Foo<bool>
 */
#define OP_UNARY_TRIVIAL_SUBCLASS(CLASS, X, ...)                                                  \
    class CLASS final : public ::Op::Unary {                                                      \
        OP_FINAL_INIT(CLASS, (X), "" __VA_ARGS__);                                                \
                                                                                                  \
      private:                                                                                    \
        /** Private constructor */                                                                \
        explicit inline CLASS(const ::Hash::Hash &h, const ::Expression::BasePtr &x)              \
            : Unary { h, static_cuid, x } {}                                                      \
    };


namespace Op {

    /** A Unary Op class */
    class Unary : public Base {
        OP_PURE_INIT(Unary);

      public:
        /** The operand */
        const Expression::BasePtr child;

        /** Add's the raw expression children of the expression to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        inline void add_reversed_children(Stack &s) const override final {
            s.emplace(child.get());
        }

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