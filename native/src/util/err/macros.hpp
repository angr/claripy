/**
 * @file
 * \ingroup util
 * @brief This file defines macros used across Util
 */
#ifndef R_SRC_UTIL_ERR_MACROS_HPP_
#define R_SRC_UTIL_ERR_MACROS_HPP_

#include "../../macros.hpp"


/** A macro used to define a non-final derived exception class
 *  This macro requires SUPER be in the same namespace
 *  Destructor is defaulted with noexcept
 */
#define UTIL_ERR_DEFINE_NONFINAL_EXCEPTION(DERIVED, SUPER)                                         \
    struct DERIVED : public SUPER {                                                                \
        SET_IMPLICITS_NONDEFAULT_CTORS(DERIVED, delete);                                           \
        /** Inherit constructors */                                                                \
        using SUPER::SUPER;                                                                        \
        /** Default virtual destructor */                                                          \
        inline ~DERIVED() noexcept override = default;                                             \
    };

/** A macro used to define a final derived subclass
 *  class which inherits its parent's constructors
 */
#define UTIL_ERR_DEFINE_FINAL_EXCEPTION(DERIVED, SUPER)                                            \
    struct DERIVED final : public SUPER {                                                          \
        /** Inherit constructors */                                                                \
        using SUPER::SUPER;                                                                        \
        /** Default virtual destructor */                                                          \
        inline ~DERIVED() noexcept final = default;                                                \
    };

/** A macro used to define a final derived exception class
 *  This macro does not require SUPER be in the same namespace
 */
#define UTIL_ERR_DEFINE_NAMESPACED_FINAL_EXCEPTION(DERIVED, SUPER, NS)                             \
    struct DERIVED final : public NS::SUPER {                                                      \
        /** Inherit constructors */                                                                \
        using NS::SUPER::SUPER;                                                                    \
        /** Default virtual destructor */                                                          \
        inline ~DERIVED() noexcept final = default;                                                \
    };


#endif
