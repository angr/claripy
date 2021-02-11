/**
 * @file
 * @brief A floating point binary Op; takes an FP mode and two inputs of the same type
 */
#ifndef __OP_FP_MODEBINARY_HPP__
#define __OP_FP_MODEBINARY_HPP__

#include "../../fp.hpp"
#include "../binary.hpp"


/** A macro used to define a trivial subclass of ModeBinary */
#define OP_FP_MODEBINARY_TRIVIAL_SUBCLASS(CLASS)                                                  \
    class CLASS final : public ModeBinary {                                                       \
        OP_FINAL_INIT(CLASS)                                                                      \
      private:                                                                                    \
        /** Private constructor */                                                                \
        explicit inline CLASS(const Hash::Hash &h, const Expression::BasePtr &l,                  \
                              const Expression::BasePtr &r, const ::FP::Mode m)                   \
            : ModeBinary { h, static_cuid, l, r, m } {}                                           \
    };


namespace Op::FP {

    /** An FP Binary Op class
     *  Operands must all be of the same type
     */
    class ModeBinary : public Binary<Expression::FP> {
        OP_PURE_INIT(ModeBinary)
      public:
        /** FP Mode */
        const ::FP::Mode mode;

      protected:
        /** Protected constructor */
        explicit inline ModeBinary(const Hash::Hash &h, const CUID::CUID &cuid_,
                                   const Expression::BasePtr &l, const Expression::BasePtr &r,
                                   const ::FP::Mode m)
            : Binary { h, cuid_, l, r }, mode { m } {}
    };

    /** Default virtual destructor */
    ModeBinary::~ModeBinary() noexcept = default;

} // namespace Op::FP

#endif
