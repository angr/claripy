/**
 * @file
 * @brief This file defines a method to create an Expr with an symbol Op
 */
#ifndef R_SRC_CREATE_SYMBOL_HPP_
#define R_SRC_CREATE_SYMBOL_HPP_

#include "constants.hpp"


namespace Create {

    /** Create a Bool Expr with an symbol op */
    inline Expr::BasePtr symbol(std::string name, Annotation::SPAV &&sp) {
        return Expr::factory<Expr::Bool>(true, Op::factory<Op::Symbol>(std::move(name)),
                                         std::move(sp));
    }

    /** Create a Expr with an symbol op
     *  This override is for sized Expr types
     */
    template <typename T>
    Expr::BasePtr symbol(std::string name, const U64 bit_length, Annotation::SPAV &&sp) {
        // Type checks
        static_assert(Util::Type::Is::ancestor<Expr::Bits, T>,
                      "Create::symbol argument types must be a subclass of Bits");
        static_assert(std::is_final_v<T>, "Create::symbol's T must be a final type");

        // Construct expr
        return Expr::factory<T>(true, Op::factory<Op::Symbol>(std::move(name)), bit_length,
                                std::move(sp));
    }

    /* A shortcut for symbol; exists for the API */
    inline Expr::BasePtr symbol_bool(std::string name, Annotation::SPAV sp = empty_spav) {
        return symbol(std::move(name), std::move(sp));
    }

    /* A shortcut for symbol<BV>; exists for the API */
    inline Expr::BasePtr symbol_bv(std::string name, const U64 bit_length,
                                   Annotation::SPAV sp = empty_spav) {
        return symbol<Expr::BV>(std::move(name), bit_length, std::move(sp));
    }

    /* A shortcut for symbol<FP>; exists for the API */
    inline Expr::BasePtr symbol_fp(std::string name, const U64 bit_length,
                                   Annotation::SPAV sp = empty_spav) {
        return symbol<Expr::FP>(std::move(name), bit_length, std::move(sp));
    }

    /* A shortcut for symbol<String>; exists for the API */
    inline Expr::BasePtr symbol_string(std::string name, const U64 bit_length,
                                       Annotation::SPAV sp = empty_spav) {
        return symbol<Expr::String>(std::move(name), bit_length, std::move(sp));
    }

    /* A shortcut for symbol<FP>; exists for the API */
    inline Expr::BasePtr symbol_vs(std::string name, const U64 bit_length,
                                   Annotation::SPAV sp = empty_spav) {
        return symbol<Expr::VS>(std::move(name), bit_length, std::move(sp));
    }

} // namespace Create

#endif
