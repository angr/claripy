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
#define OP_UNARY_TRIVIAL_SUBCLASS(CLASS, ...)                                                     \
    class CLASS final : public ::Op::Unary<__VA_ARGS__> {                                         \
        OP_FINAL_INIT(CLASS)                                                                      \
      private:                                                                                    \
        /** Private constructor */                                                                \
        explicit inline CLASS(const ::Hash::Hash &h, const ::Expression::BasePtr &x)              \
            : Unary { h, static_cuid, x } {}                                                      \
    };


namespace Op {

    /** A unary Base op class
     *  All templated unary classes must subclass this
     *  To check if a class is unary, check if it subclasses UnaryBase
     */
    struct UnaryBase : public Base {
        /** Use parent constructors */
        using Base::Base;
        OP_PURE_INIT(UnaryBase)
    };
    /** Default destructor */
    UnaryBase::~UnaryBase() noexcept = default;

    /** A Unary Op class
     *  Operands must all be of the same type
     *	Will verify that child is a subclasses T
     */
    template <typename T = Expression::Base> class Unary : public UnaryBase {
        OP_PURE_INIT(Unary)
      public:
        /** The operand */
        const Expression::BasePtr child;

      protected:
        /** Protected constructor */
        explicit inline Unary(const Hash::Hash &h, const CUID::CUID &cuid_,
                              const Expression::BasePtr &x)
            : UnaryBase { h, cuid_ }, child { x } {
            using Err = Error::Expression::Type;

            // Type check
            Utils::affirm<Err>(Expression::is_t<T, true>(child),
                               "Op::Unary child does not subclass T");
        }
    };

    /** Default virtual destructor */
    template <typename T> Unary<T>::~Unary() noexcept = default;

} // namespace Op

#endif
