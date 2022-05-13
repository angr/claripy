/**
 * @file
 * @brief This file defines compile-time Hashes of types (not instances of types)
 * TODO: add test cases for this in sanity check
 */
#ifndef R_SRC_HASH_TYPE_HPP_
#define R_SRC_HASH_TYPE_HPP_

#include "strict_type.hpp"

namespace Hash {

    namespace Private {
        template <typename... Args> constexpr Hash type_() noexcept {
            unsigned i { 0 };
            Hash arr[sizeof...(Args)] = { 0 }; // Default initialize for compiler
            (static_cast<void>(arr[i++] = strict_type<Util::Type::RemoveCVR<Args>>), ...);
            return Util::FNV1a<Hash>::template hash<Hash>(arr, sizeof...(Args));
        };
    } // namespace Private

    /** A hash of the types Args with reference and cv qualifiers removed */
    template <typename... Args> inline const constexpr Hash type { Private::type_<Args...>() };

} // namespace Hash

#endif
