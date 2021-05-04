/**
 * @file
 * @brief This file defines trivial subclasses of Base and Bits
 */
#ifndef __EXPRESSION_INSTANTIABLES_HPP__
#define __EXPRESSION_INSTANTIABLES_HPP__

#include "bits.hpp"


/** Local: A macro to declare trivial subclasses of Bits */
#define BITS_SUBCLASS(CLASS)                                                                      \
    /** An Expression::Bits subclass */                                                           \
    class CLASS final : public Bits {                                                             \
        FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(::Expression::Base, 0)                              \
      public:                                                                                     \
        /** Default destructor */                                                                 \
        inline ~CLASS() noexcept override final = default;                                        \
        /** Type name */                                                                          \
        inline Constants::CCSC type_name() const override final { return #CLASS; }                \
        /** Python's repr function */                                                             \
        void repr(std::ostringstream &out, const bool verbose = false) const override final;      \
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
        SET_IMPLICITS_CONST_MEMBERS(CLASS, delete);                                               \
    };


namespace Expression {

    /** An Expression::Base subclass representing a bool */
    class Bool final : public Base {
        FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(::Expression::Base, 0)
      public:
        /** Default destructor */
        inline ~Bool() noexcept override final = default;
        /** Type name */
        inline Constants::CCSC type_name() const override final { return "Bool"; }
        /** Python's repr function */
        void repr(std::ostringstream &out, const bool verbose = false) const override final;

      private:
        /** Private Constructor */
        explicit inline Bool(const Hash::Hash h, AnVec &&ans, const bool sym,
                             Op::BasePtr &&op_) noexcept
            : Base { h, static_cuid, std::forward<AnVec>(ans), sym,
                     std::forward<Op::BasePtr>(op_) } {}
        /* Disable other methods of construction */
        SET_IMPLICITS_CONST_MEMBERS(Bool, delete);
    };

    // Bits subclasses
    BITS_SUBCLASS(String)
    BITS_SUBCLASS(VS)
    BITS_SUBCLASS(BV)
    BITS_SUBCLASS(FP)

} // namespace Expression


// Cleanup
#undef BITS_SUBCLASS


#endif
