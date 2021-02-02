/**
 * @file
 * \ingroup utils
 * @brief This file defines a set of methods used to cast pointers
 */
#ifndef __UTILS_POINTERCAST_HPP__
#define __UTILS_POINTERCAST_HPP__

#include "affirm.hpp"
#include "error.hpp"

#include <memory>
#include <type_traits>


namespace Utils {

    /** An up cast */
    template <typename In, typename Out>
    constexpr inline Out up_cast(const std::shared_ptr<In> &in) noexcept {
        static_assert(std::is_base_of_v<Out, In>, "up_cast passed invalid <In, Out> type pair");
        return std::static_pointer_cast<Out>(in); // Does its own checks as well
    }

    /** A dynamic down cast */
    template <typename In, typename Out>
    constexpr inline Out dynamic_down_cast(const std::shared_ptr<In> &in) noexcept {
        static_assert(std::is_base_of_v<In, Out>,
                      "dynamic_down_cast passed invalid <In, Out> type pair");
        return std::dynamic_pointer_cast<Out>(in); // Does its own checks as well
    }

    /** A dynamic side cast
     *  Warning: No static checks used
     */
    template <typename In, typename Out>
    constexpr inline Out dynamic_side_cast(const std::shared_ptr<In> &in) noexcept {
        return std::dynamic_pointer_cast<Out>(in); // Does its own checks as well
    }

    /** Dynamic down-cast that throws on failure */
    template <typename In, typename Out>
    constexpr inline Out dynamic_down_cast_throw_on_fail(const std::shared_ptr<In> &in) noexcept {
        const auto ret = dynamic_down_cast<Out>(in);
        affirm<Error::Unexpected::BadCast>(ret != nullptr, "Dynamic down-cast failed");
        return ret;
    }

    /** A dynamic side cast that throws on failure */
    template <typename In, typename Out>
    constexpr inline Out dynamic_side_cast_throw_on_fail(const std::shared_ptr<In> &in) noexcept {
        const auto ret = dynamic_side_cast<Out>(in);
        affirm<Error::Unexpected::BadCast>(ret != nullptr, "Dynamic down-cast failed");
        return ret;
    }

    // Functions that throw

    /** An static down cast
     *  Is dynamic and throws on failure during debugging
     */
    template <typename In, typename Out>
    constexpr inline Out static_down_cast(const std::shared_ptr<In> &in)
#ifdef DEBUG
    {
        return dynamic_down_cast<Out>(in);
    }
#else
        noexcept {
        static_assert(std::is_base_v<In, Out>,
                      "static_down_cast passed invalid <In, Out> type pair");
        return std::static_pointer_cast<Out>(in); // Does its own checks as well
    }
#endif

    /** An static side cast
     *  Is dynamic and throws on failure during debugging
     */
    template <typename In, typename Out>
    constexpr inline Out static_side_cast(const std::shared_ptr<In> &in)
#ifdef DEBUG
    {
        return dynamic_side_cast<Out>(in);
    }
#else
        noexcept {
        return std::static_pointer_cast<Out>(in);
    }
#endif


} // namespace Utils

#endif
