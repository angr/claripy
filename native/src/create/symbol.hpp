/**
 * @file
 * @brief This file defines a method to create an Expr with an symbol Op
 */
#ifndef R_SRC_CREATE_SYMBOL_HPP_
#define R_SRC_CREATE_SYMBOL_HPP_

#include "constants.hpp"


namespace Create {

    /** Create an Expr with a symbol op with annotations */
    template <typename T, typename... Args>
    Expr::BasePtr symbol(std::string &&name, const U64 bit_length, Args &&...args) {
        static_assert(Util::Type::Is::ancestor<Expr::Bits, T>,
                      "Create::symbol argument types must be a subclass of Base");
        static_assert(std::is_final_v<T>, "Create::symbol's T must be a final type");
        // Append SPAV if needed
        if constexpr (sizeof...(Args) == 0) {
            return Expr::factory<T>(true, Op::factory<Op::Symbol>(std::move(name)),
                                    std::move(bit_length), std::move(empty_spav));
        }
        else {
            return Expr::factory<T>(true, Op::factory<Op::Symbol>(std::move(name)),
                                    std::move(bit_length), std::forward<Args>(args)...);
        }
    }

    /** Create an Expr with a symbol op */
    template <typename... Args> Expr::BasePtr symbol(std::string &&name, Args &&...args) {
        if constexpr (sizeof...(Args) == 0) {
            return Expr::factory<Expr::Bool>(true, Op::factory<Op::Symbol>(std::move(name)),
                                             std::move(empty_spav));
        }
        else {
            return Expr::factory<Expr::Bool>(true, Op::factory<Op::Symbol>(std::move(name)),
                                             std::forward<Args>(args)...);
        }
    }

    // Non-templated non-moving functions (the API can use these)

    /** Create a Bool Expr with a symbol op */
    inline Expr::BasePtr symbol_bool(std::string name, Annotation::SPAV sp = empty_spav) {
        return Expr::factory<Expr::Bool>(true, Op::factory<Op::Symbol>(std::move(name)),
                                         std::move(sp));
    }

#define M_BITS_TYPE(TYPE, NAME)                                                                    \
    inline Expr::BasePtr symbol_##NAME(std::string name, const U64 bit_length,                     \
                                       Annotation::SPAV sp = empty_spav) {                         \
        return Expr::factory<Expr::TYPE>(true, Op::factory<Op::Symbol>(std::move(name)),           \
                                         std::move(bit_length), std::move(sp));                    \
    }

    /** Create a String Expr with a symbol op */
    M_BITS_TYPE(String, string);
    /** Create a BV Expr with a symbol op */
    M_BITS_TYPE(BV, bv);
    /** Create a FP Expr with a symbol op */
    M_BITS_TYPE(FP, fp);
    /** Create a VS Expr with a symbol op */
    M_BITS_TYPE(VS, vs);

#undef M_BITS_TYPE

} // namespace Create

#endif
