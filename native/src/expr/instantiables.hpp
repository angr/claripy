/**
 * @file
 * @brief This file defines trivial subclasses of Base and Bits
 */
#ifndef R_EXPR_INSTANTIABLES_HPP_
#define R_EXPR_INSTANTIABLES_HPP_

#include "bits.hpp"


/** Local: A macro to declare trivial subclasses of Bits */
#define BITS_SUBCLASS(CLASS)                                                                       \
    /** An Expr::Bits subclass */                                                                  \
    class CLASS final : public Bits {                                                              \
        FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(::Expr::Base, 0)                                     \
      public:                                                                                      \
        /** Default destructor */                                                                  \
        inline ~CLASS() noexcept final = default;                                                  \
        /** Get the type name */                                                                   \
        virtual inline const char *type_name() const noexcept final { return #CLASS; }             \
                                                                                                   \
      private:                                                                                     \
        /** Private Constructor */                                                                 \
        explicit inline CLASS(const Hash::Hash h, const bool sym, Op::BasePtr &&op_,               \
                              const UInt bit_length_, Annotation::SPAV &&sp) noexcept              \
            : Bits { h, static_cuid, sym, std::move(op_), bit_length_, std::move(sp) } {}          \
        /* Disable other methods of construction */                                                \
        SET_IMPLICITS_CONST_MEMBERS(CLASS, delete);                                                \
    };


namespace Expr {

    /** An Expr::Base subclass representing a bool */
    class Bool final : public Base {
        FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(::Expr::Base, 0)
      public:
        /** Default destructor */
        inline ~Bool() noexcept final = default;
        /** Get the type name */
        virtual inline const char *type_name() const noexcept final { return "Bool"; }

      private:
        /** Private Constructor */
        explicit inline Bool(const Hash::Hash h, const bool sym, Op::BasePtr &&op_,
                             Annotation::SPAV &&sp) noexcept
            : Base { h, static_cuid, sym, std::move(op_), std::move(sp) } {}
        /* Disable other methods of construction */
        SET_IMPLICITS_CONST_MEMBERS(Bool, delete);
    };

    // Bits subclasses
    BITS_SUBCLASS(String)
    BITS_SUBCLASS(VS)
    BITS_SUBCLASS(BV)
    BITS_SUBCLASS(FP)

} // namespace Expr


// Cleanup
#undef BITS_SUBCLASS


#endif
