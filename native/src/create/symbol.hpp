/**
 * @file
 * @brief This file defines a method to create an Expr with a symbol Op
 */
#ifndef R_SRC_CREATE_SYMBOL_HPP_
#define R_SRC_CREATE_SYMBOL_HPP_

#include "constants.hpp"


namespace Create {

    namespace Private {
        template <typename T, typename... Args> constexpr bool is_u64() {
            return (sizeof...(Args) == 0) && std::is_same_v<U64, Util::Type::RemoveCVR<T>>;
        };
    } // namespace Private

    /** Create an Expr with a symbol op with annotations */
    template <typename T, typename... Args>
    Expr::BasePtr symbol(std::string &&name, Expr::OpPyDict d, Args &&...args) {
        static_assert(Util::Type::Is::ancestor<Expr::Bits, T>,
                      "Create::symbol argument types must be a subclass of Base");
        static_assert(std::is_final_v<T>, "Create::symbol's T must be a final type");
        if constexpr (sizeof...(Args) > 0) {
            static_assert(Private::is_u64<Args...>(), "Args... should be a U64");
        }
        return Expr::factory<T>(true, Op::factory<Op::Symbol>(std::move(name)), std::move(d),
                                std::forward<Args>(args)...);
    }

    /** Create an Expr with a symbol op */
    template <typename... Args> Expr::BasePtr symbol(std::string &&name, Args &&...args) {
        return Expr::factory<Expr::Bool>(true, Op::factory<Op::Symbol>(std::move(name)),
                                         std::forward<Args>(args)...);
    }

    // Non-templated non-moving functions (the API can use these)

    /** Create a Bool Expr with a symbol op */
    inline Expr::BasePtr symbol_bool(std::string name, Expr::OpPyDict d = {}) {
        return Expr::factory<Expr::Bool>(true, Op::factory<Op::Symbol>(std::move(name)),
                                         std::move(d));
    }

    /** Create a String Expr with a symbol op
     *  Note: length is taken in as a byte length, not a bit length
     */
    inline Expr::BasePtr symbol_string(std::string name, const U64 byte_length,
                                       Expr::OpPyDict d = {}) {
        return Expr::factory<Expr::String>(true, Op::factory<Op::Symbol>(std::move(name)),
                                           std::move(d), CHAR_BIT * byte_length);
    }

#define M_BITS_TYPE(TYPE, NAME)                                                                    \
    inline Expr::BasePtr symbol_##NAME(std::string name, const U64 bit_length,                     \
                                       Expr::OpPyDict d = {}) {                                    \
        return Expr::factory<Expr::TYPE>(true, Op::factory<Op::Symbol>(std::move(name)),           \
                                         std::move(d), bit_length);                                \
    }

    /** Create a BV Expr with a symbol op */
    M_BITS_TYPE(BV, bv);
    /** Create a FP Expr with a symbol op
     *  TODO: later allow Width instead of bit_length
     */
    M_BITS_TYPE(FP, fp);
    /** Create a VS Expr with a symbol op */
    M_BITS_TYPE(VS, vs);

#undef M_BITS_TYPE

} // namespace Create

#endif
