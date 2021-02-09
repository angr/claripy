/**
 * @file
 * \ingroup utils
 * @brief This file defines private pointer cast methods
 * These methods preserve the constness of the internal type
 */
#ifndef __UTILS_PRIVATE_POINTERCAST_HPP__
#define __UTILS_PRIVATE_POINTERCAST_HPP__

#include "../transfer_const.hpp"

#include <memory>
#include <type_traits>


namespace Utils::Private {

    /** A const preserving static pointer cast */
    template <typename Out, typename In>
    constexpr inline auto static_pointer_cast(const std::shared_ptr<In> &in) noexcept {
        if constexpr (!is_exactly_same<In, Out>) {
            return std::static_pointer_cast<TransferConst<Out, In>>(in);
        }
        else {
            return in;
        }
    }

    /** An unchecked dynamic pointer cast */
    template <typename Out, typename In>
    constexpr inline auto dynamic_pointer_cast(const std::shared_ptr<In> &in) noexcept {
        if constexpr (!is_same_ignore_const<In, Out>) {
            return std::dynamic_pointer_cast<TransferConst<Out, In>>(in);
        }
        else {
            return Private::static_pointer_cast<Out>(in);
        }
    }

} // namespace Utils::Private

#endif
