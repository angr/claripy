/**
 * @file
 * @brief This file defines compile-time Hashes of types (not instances of types)
 */
#ifndef R_SRC_HASH_STRICTTYPE_HPP_
#define R_SRC_HASH_STRICTTYPE_HPP_

#include "constants.hpp"

#include "../cuid.hpp"
#include "../mode.hpp"
#include "../util.hpp"


namespace Hash {

    namespace Private {
        template <typename T> constexpr Hash try_cuid() {
            static_assert(CUID::has_static_cuid<T>, "No defined type-hash or static_cuid");
            return T::static_cuid;
        }
    } // namespace Private

    template <typename T> static inline const constexpr Hash strict_type { Private::try_cuid<T>() };

#define M_T_HASH(TYPE)                                                                             \
    template <> static inline const constexpr Hash strict_type<TYPE> {                             \
        UTIL_FILE_LINE_HASH                                                                        \
    }

#define M_T_HASH_TEMPLATE(TEMP_TYPE)                                                               \
    template <typename T>                                                                          \
    static inline const constexpr Hash strict_type<TEMP_TYPE<T>> { HASH_CANTOR(                    \
        UTIL_FILE_LINE_HASH, strict_type<Util::Type::RemoveCVR<T>>) };

    // Containers
    M_T_HASH_TEMPLATE(std::shared_ptr)
    M_T_HASH_TEMPLATE(std::vector)

    // Types
    M_T_HASH(Mode::FP::Rounding);
    M_T_HASH(Mode::FP::Width);
    M_T_HASH(std::string);

    // Integral types
    M_T_HASH(long long);
    M_T_HASH(uint32_t);
    M_T_HASH(uint16_t);
    M_T_HASH(uint8_t);
    M_T_HASH(U64);

    // Primitives
    M_T_HASH(const char *);
    M_T_HASH(double);
    M_T_HASH(float);
    M_T_HASH(bool);

#undef M_T_HASH_TEMPLATE
#undef M_T_HASH

} // namespace Hash

#endif
