/**
 * @file
 * \ingroup utils
 * @brief This file defines a set of methods used to cast pointers
 * These casts preserve the const-ness of the internal type
 */
#ifndef R_UTILS_POINTERCAST_HPP_
#define R_UTILS_POINTERCAST_HPP_

#include "affirm.hpp"
#include "error.hpp"
#include "full.hpp"
#include "is_ancestor.hpp"
#include "private/pointer_cast.hpp"

#include "../constants.hpp"

#include <memory>
#include <type_traits>


namespace Utils {

    /** An up cast */
    template <typename Out, typename In>
    constexpr auto up_cast(const std::shared_ptr<In> &in) noexcept {
        static_assert(is_ancestor<Out, In>, "up_cast passed invalid <In, Out> type pair");
        return Private::static_pointer_cast<Out>(in); // Does its own checks as well
    }

    /** A dynamic down cast */
    template <typename Out, typename In>
    constexpr auto dynamic_down_cast(const std::shared_ptr<In> &in) noexcept {
        static_assert(is_ancestor<In, Out>,
                      "dynamic_down_cast passed invalid <In, Out> type pair");
        return Private::dynamic_pointer_cast<Out>(in); // Does its own checks as well
    }

    /** A dynamic side cast
     *  Warning: No static checks used
     */
    template <typename Out, typename In>
    constexpr auto dynamic_side_cast(const std::shared_ptr<In> &in) noexcept {
        return Private::dynamic_pointer_cast<Out>(in); // Does its own checks as well
    }

    /** Dynamic down-cast that throws on failure */
    template <typename Out, typename In, typename Err = Error::Unexpected::BadCast>
    constexpr auto dynamic_down_cast_throw_on_fail(const std::shared_ptr<In> &in) noexcept {
        const auto ret = dynamic_down_cast<Out>(in);
        affirm<Err>(full(ret), WHOAMI_WITH_SOURCE "Dynamic down-cast failed");
        return ret;
    }

    /** A dynamic side cast that throws on failure */
    template <typename Out, typename In, typename Err = Error::Unexpected::BadCast>
    constexpr auto dynamic_side_cast_throw_on_fail(const std::shared_ptr<In> &in) noexcept {
        const auto ret = dynamic_side_cast<Out>(in);
        affirm<Err>(full(ret), WHOAMI_WITH_SOURCE "Dynamic side-cast failed");
        return ret;
    }

    // Functions that throw

    /** An static down cast
     *  Is dynamic and throws on failure during debugging
     */
    template <typename Out, typename In>
    constexpr auto static_down_cast(const std::shared_ptr<In> &in)
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
    constexpr auto static_side_cast(const std::shared_ptr<In> &in)
#ifdef DEBUG
    {
        return dynamic_side_cast<Out>(in);
    }
#else
        noexcept {
        return Private::static_pointer_cast<Out>(in);
    }
#endif

    /** Return true if in is an Out
     *  Warning: We return false if the pointer points to nullptr
     *  Note: this does not do any static assertion verification itself
     */
    template <typename Out, typename In>
    constexpr bool dynamic_test(const std::shared_ptr<In> &in) {
        return dynamic_cast<Constants::CTSC<Out>>(in.get()) != nullptr;
    }

    /** Return true if the dynamic cast desired will pass
     *  Warning: We throw if the pointer points to nullptr
     *  Note: this does not do any static assertion verification itself
     *  Note: This requires the type of exception to be thrown to be passed
     */
    template <typename To, typename Err, typename In, typename... Args>
    constexpr void dynamic_test_throw_on_fail(const std::shared_ptr<In> &in, const Args &...args) {
        affirm<Err>(dynamic_test<To>(in), args...);
    }

} // namespace Utils

#endif
