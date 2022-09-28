/**
 * @file
 * @brief This file defines trivial subclasses of Base and Bits
 */
#ifndef R_SRC_EXPR_INSTANTIABLES_HPP_
#define R_SRC_EXPR_INSTANTIABLES_HPP_

#include "bits.hpp"


#define M_SUBCLASS(CLASS, BASE_T)                                                                  \
    /** An Expr type */                                                                            \
    class CLASS final : public BASE_T {                                                            \
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
        template <typename... Args>                                                                \
        explicit inline CLASS(const Hash::Hash h, Args &&...args) noexcept                         \
            : BASE_T { h, static_cuid, std::forward<Args>(args)... } {}                            \
        /* Disable other methods of construction */                                                \
        SET_IMPLICITS_CONST_MEMBERS(CLASS, delete);                                                \
    }


namespace Expr {
    M_SUBCLASS(Bool, Base);
    M_SUBCLASS(String, Bits);
    M_SUBCLASS(VS, Bits);
    M_SUBCLASS(BV, Bits);
    M_SUBCLASS(FP, Bits);
} // namespace Expr

#undef M_BITS_SUBCLASS

#endif
