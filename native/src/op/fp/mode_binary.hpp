/**
 * @file
 * @brief A floating point binary Op; takes an FP mode and two inputs of the same type
 */
#ifndef __OP_FP_MODEBINARY_HPP__
#define __OP_FP_MODEBINARY_HPP__

#include "../../mode.hpp"
#include "../binary.hpp"


/** A macro used to define a trivial subclass of ModeBinary
 *  An additional argument can be passed as the prefix to the desired debug name of the class
 *  For example, "FP::" may be desired for an FP op
 *  X can be anything, but must be different between different templates of the same class
 *  For example, Foo<int> must give a different X from Foo<bool>
 */
#define OP_FP_MODEBINARY_TRIVIAL_SUBCLASS(CLASS, X, ...)                                          \
    class CLASS final : public ModeBinary {                                                       \
        OP_FINAL_INIT(CLASS, (X), "" __VA_ARGS__);                                                \
                                                                                                  \
      private:                                                                                    \
        /** Private constructor */                                                                \
        explicit inline CLASS(const ::Hash::Hash &h, const ::Expression::BasePtr &l,              \
                              const ::Expression::BasePtr &r, const ::Mode::FP m)                 \
            : ModeBinary { h, static_cuid, l, r, m } {}                                           \
    };


namespace Op::FP {

    /** An FP Binary Op class
     *  Operands must all be of the same type and size
     */
    class ModeBinary : public Base {
        OP_PURE_INIT(ModeBinary);

      public:
        /** FP Mode */
        const Mode::FP mode;
        /** Left operand */
        const Expression::BasePtr left;
        /** Right operand */
        const Expression::BasePtr right;

        /** Add's the raw expression children of the expression to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        inline void add_reversed_children(Stack &s) const override final {
            s.emplace(right.get());
            s.emplace(left.get());
        }

      protected:
        /** Protected constructor */
        explicit inline ModeBinary(const Hash::Hash &h, const CUID::CUID &cuid_,
                                   const Expression::BasePtr &l, const Expression::BasePtr &r,
                                   const Mode::FP m)
            : Base { h, cuid_ }, mode { m }, left { l }, right { r } {
            using Err = Error::Expression::Type;
            Utils::affirm<Err>(Expression::are_same_type<true>(left, right),
                               WHOAMI_WITH_SOURCE "left and right types or sizes differ");
        }
    };

    /** Default virtual destructor */
    ModeBinary::~ModeBinary() noexcept = default;

    /** Returns true if T is ModeBinary */
    template <typename T> UTILS_ICCBOOL is_mode_binary { Utils::is_ancestor<ModeBinary, T> };

} // namespace Op::FP

#endif
