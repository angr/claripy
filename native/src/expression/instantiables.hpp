/**
 * @file
 * @brief This file defines trivial subclasses of Base and Bits
 */
#ifndef __EXPRESSION_INSTANTIABLES_HPP__
#define __EXPRESSION_INSTANTIABLES_HPP__

#include "bits.hpp"


/** Local: A macro to declare trivial subclasses of Bits */
#define BITS_SUBCLASS(CLASS)                                                                      \
    /** This class is an Expression subclass */                                                   \
    class CLASS final : public Bits {                                                             \
        FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(::Expression::Base)                                 \
      public:                                                                                     \
        /** Default destructor */                                                                 \
        inline ~CLASS() noexcept override final = default;                                        \
                                                                                                  \
      private:                                                                                    \
        /** Private Constructor */                                                                \
        explicit inline CLASS(const Hash::Hash h, AnVec &&ans, const bool sym, Op::BasePtr &&op_, \
                              const Constants::UInt bit_length_) noexcept                         \
            : Bits { h,                                                                           \
                     static_cuid,                                                                 \
                     std::forward<AnVec>(ans),                                                    \
                     sym,                                                                         \
                     std::forward<Op::BasePtr>(op_),                                              \
                     bit_length_ } {}                                                             \
        /* Disable other methods of construction */                                               \
        SET_IMPLICITS_CONST_MEMBERS(CLASS, delete)                                                \
    };


namespace Expression {
    BITS_SUBCLASS(String)
    BITS_SUBCLASS(VS)
    BITS_SUBCLASS(BV)
    BITS_SUBCLASS(FP)
} // namespace Expression


// Cleanup
#undef BITS_SUBCLASS


#endif
