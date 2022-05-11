/**
 * @file
 * @brief This file defines compile-time Hashes of types (not instances of types)
 * TODO: add test cases for this in sanity check
 */
#ifndef R_SRC_HASH_TYPE_HPP_
#define R_SRC_HASH_TYPE_HPP_

#include "strict_type.hpp"


namespace Hash {

    template <typename... Args> static constexpr Hash type_() noexcept {
        unsigned i { 0 };
        Hash arr[sizeof...(Args)];
        (static_cast<void>(arr[i++] = strict_type<Util::Type::RemoveCVR<Args>>), ...);
        return Util::FNV1a<Hash>::template hash<Hash>(arr, sizeof...(Args));
    };

    template <typename... Args> static inline const constexpr Hash type { type_<Args...>() };

} // namespace Hash

#endif
