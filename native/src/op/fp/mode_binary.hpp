/**
 * @file
 * @brief A floating point binary Op; takes an FP mode and two inputs of the same type
 */
#ifndef __OP_FP_MODEBINARY_HPP__
#define __OP_FP_MODEBINARY_HPP__

#include "../../mode.hpp"
#include "../binary.hpp"


/** A macro used to define a trivial subclass of ModeBinary */
#define OP_FP_MODEBINARY_TRIVIAL_SUBCLASS(CLASS)                                                  \
    class CLASS final : public ModeBinary {                                                       \
        OP_FINAL_INIT(CLASS)                                                                      \
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
        OP_PURE_INIT(ModeBinary)
      public:
        /** FP Mode */
        const Mode::FP mode;
        /** Left operand */
        const Expression::BasePtr left;
        /** Right operand */
        const Expression::BasePtr right;

      protected:
        /** Protected constructor */
        explicit inline ModeBinary(const Hash::Hash &h, const CUID::CUID &cuid_,
                                   const Expression::BasePtr &l, const Expression::BasePtr &r,
                                   const Mode::FP m)
            : Base { h, cuid_ }, mode { m }, left { l }, right { r } {
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
