/**
 * @file
 * @brief This file defines trivial subclasses of Base and Bits
 */
#ifndef R_SRC_EXPR_INSTANTIABLES_HPP_
#define R_SRC_EXPR_INSTANTIABLES_HPP_

#include "bits.hpp"


#define M_BITS_SUBCLASS(CLASS)                                                                     \
    /** An Expr::Bits subclass */                                                                  \
    class CLASS final : public Bits {                                                              \
        FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(::Expr::Base)                                        \
      public:                                                                                      \
        /** Default destructor */                                                                  \
        inline ~CLASS() noexcept final = default;                                                  \
        /** The type name */                                                                       \
        static constexpr const char *static_type_name { #CLASS };                                  \
        /** Get the type name */                                                                   \
        virtual inline const char *type_name() const noexcept final { return static_type_name; }   \
                                                                                                   \
      private:                                                                                     \
        /** Private Constructor */                                                                 \
        explicit inline CLASS(const Hash::Hash h, const bool sym, Op::BasePtr &&op_,               \
                              const U64 bit_length_, Annotation::SPAV &&sp) noexcept               \
            : Bits { h, static_cuid, sym, std::move(op_), bit_length_, std::move(sp) } {}          \
        /* Disable other methods of construction */                                                \
        SET_IMPLICITS_CONST_MEMBERS(CLASS, delete);                                                \
    };


namespace Expr {

    /** An Expr::Base subclass representing a bool */
    class Bool final : public Base {
        FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(::Expr::Base)
      public:
        /** Default destructor */
        inline ~Bool() noexcept final = default;
        /** The type name */
        static constexpr const char *static_type_name { "Bool" };
        /** Get the type name */
        virtual inline const char *type_name() const noexcept final { return static_type_name; }

      private:
        /** Private Constructor */
        explicit inline Bool(const Hash::Hash h, const bool sym, Op::BasePtr &&op_,
                             Annotation::SPAV &&sp) noexcept
            : Base { h, static_cuid, sym, std::move(op_), std::move(sp) } {}
        /* Disable other methods of construction */
        SET_IMPLICITS_CONST_MEMBERS(Bool, delete);
    };

    // Bits subclasses
    M_BITS_SUBCLASS(String)
    M_BITS_SUBCLASS(VS)
    M_BITS_SUBCLASS(BV)
    M_BITS_SUBCLASS(FP)
#undef M_BITS_SUBCLASS

} // namespace Expr


#endif
