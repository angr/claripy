/**
 * @file
 * \ingroup utils
 * @brief This file defines a set of methods used to cast pointers
 * These casts preserve the constness of the internal type
 */
#ifndef __UTILS_POINTERCAST_HPP__
#define __UTILS_POINTERCAST_HPP__

#include "affirm.hpp"
#include "error.hpp"
#include "full.hpp"
#include "is_ancestor.hpp"
#include "private/pointer_cast.hpp"

#include <memory>
#include <type_traits>


namespace Utils {

    /** An up cast */
    template <typename Out, typename In>
    constexpr inline auto up_cast(const std::shared_ptr<In> &in) noexcept {
        static_assert(is_ancestor<Out, In>, "up_cast passed invalid <In, Out> type pair");
        return Private::static_pointer_cast<Out>(in); // Does its own checks as well
    }

    /** An unchecked dynamic pointer cast
     *  Warning: Use this only if all other pointer casts cannot be used
     */
    template <typename Out, typename In>
    constexpr inline auto dynamic_pointer_cast(const std::shared_ptr<In> &in) noexcept {
        if constexpr (!is_same_ignore_const<In, Out>) {
            return std::dynamic_pointer_cast<TransferConst<Out, In>>(in);
        }
        else {
            return in;
        }
    }

    /** A dynamic down cast */
    template <typename Out, typename In>
    constexpr inline auto dynamic_down_cast(const std::shared_ptr<In> &in) noexcept {
        static_assert(is_ancestor<In, Out>,
                      "dynamic_down_cast passed invalid <In, Out> type pair");
        return Utils::dynamic_pointer_cast<Out>(in); // Does its own checks as well
    }

    /** A dynamic side cast
     *  Warning: No static checks used
     */
    template <typename Out, typename In>
    constexpr inline auto dynamic_side_cast(const std::shared_ptr<In> &in) noexcept {
        return Utils::dynamic_pointer_cast<Out>(in); // Does its own checks as well
    }

    /** Dynamic down-cast that throws on failure */
    template <typename Out, typename In>
    constexpr inline auto dynamic_down_cast_throw_on_fail(const std::shared_ptr<In> &in) noexcept {
        const auto ret = dynamic_down_cast<Out>(in);
        affirm<Error::Unexpected::BadCast>(empty(ret), "Dynamic down-cast failed");
        return ret;
    }

    /** A dynamic side cast that throws on failure */
    template <typename Out, typename In>
    constexpr inline auto dynamic_side_cast_throw_on_fail(const std::shared_ptr<In> &in) noexcept {
        const auto ret = dynamic_side_cast<Out>(in);
        affirm<Error::Unexpected::BadCast>(empty(ret), "Dynamic side-cast failed");
        return ret;
    }

    // Functions that throw

    /** An static down cast
     *  Is dynamic and throws on failure during debugging
     */
    template <typename Out, typename In>
    constexpr inline auto static_down_cast(const std::shared_ptr<In> &in)
#ifdef DEBUG
    {
        return dynamic_down_cast<Out>(in);
    }
#else
        noexcept {
        static_assert(is_ancestor<In, Out>, "static_down_cast passed invalid <In, Out> type pair");
        return Private::static_pointer_cast<Out>(in); // Does its own checks as well
    }
#endif

    /** An static side cast
     *  Is dynamic and throws on failure during debugging
     */
    template <typename Out, typename In>
    constexpr inline auto static_side_cast(const std::shared_ptr<In> &in)
#ifdef DEBUG
    {
        return dynamic_side_cast<Out>(in);
    }
#else
        noexcept {
        return Private::static_pointer_cast<Out>(in);
    }
#endif

    /** Return true if the dynamic cast desired will pass
     *  Note: this does not static assertion verification itself
     */
    template <typename Out, typename In>
    constexpr inline auto dynamic_test(const std::shared_ptr<In> &in) {
        return full(Utils::dynamic_pointer_cast<Out>(in));
    }

    /** Return true if the dynamic cast desired will pass
     *  Note: this does not static assertion verification itself
     */
    template <typename To, typename In, typename... Args>
    constexpr inline void dynamic_test_throw_on_fail(const std::shared_ptr<In> &in,
                                                     const Args &...args) {
        affirm<Error::Unexpected::BadCast>(dynamic_test<To>(in), args...);
    }

} // namespace Utils

#endif
