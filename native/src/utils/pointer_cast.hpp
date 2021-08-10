/**
 * @file
 * \ingroup utils
 * @brief This file defines a set of methods used to cast pointers
 * These casts preserve the const-ness of the internal type
 */
#ifndef R_UTILS_POINTERCAST_HPP_
#define R_UTILS_POINTERCAST_HPP_

#include "affirm.hpp"
#include "affirm_not_null_debug.hpp"
#include "error.hpp"
#include "full.hpp"
#include "is_ancestor.hpp"
#include "is_in.hpp"
#include "private/pointer_cast.hpp"

#include "../constants.hpp"

#include <memory>
#include <type_traits>


namespace Utils::Cast {

    namespace Dynamic {

        /** A dynamic down cast */
        template <typename Out, typename In>
        constexpr auto down(const std::shared_ptr<In> &in) noexcept {
            static_assert(is_ancestor<In, Out>,
                          "dynamic_down_cast passed invalid <In, Out> type pair");
            return Utils::Private::dynamic_pointer_cast<Out>(in); // Does its own checks as well
        }

        /** A dynamic side cast
         *  Warning: Use up / down cast functions if applicable
         */
        template <typename Out, typename In>
        constexpr auto side(const std::shared_ptr<In> &in) noexcept {
            return Utils::Private::dynamic_pointer_cast<Out>(in); // Does its own checks as well
        }

        /** Return true if in is an Out; in may not be nullptr
         *  Warning: We return false if the pointer points to nullptr
         *  Note: this does not do any static assertion verification
         */
        template <typename Out, typename In> constexpr bool test(const std::shared_ptr<In> &in) {
            UTILS_AFFIRM_NOT_NULL_DEBUG(in);
            using Ptr = Constants::CTSC<TransferConst<Out, In>>;
            return dynamic_cast<Ptr>(in.get()) != nullptr;
        }

        /** Dynamic down-cast that throws on failure; in may not be nullptr */
        template <typename Out, typename In, typename Err = Error::Unexpected::BadCast>
        constexpr auto down_throw_on_fail(const std::shared_ptr<In> &in) noexcept {
            UTILS_AFFIRM_NOT_NULL_DEBUG(in);
            auto ret { down<Out>(in) }; // Not const for possible move ret
            affirm<Err>(full(ret), WHOAMI_WITH_SOURCE "Dynamic down-cast failed");
            return ret;
        }

        /** A dynamic side cast that throws on failure; in may not be nullptr */
        template <typename Out, typename In, typename Err = Error::Unexpected::BadCast>
        constexpr auto side_throw_on_fail(const std::shared_ptr<In> &in) noexcept {
            UTILS_AFFIRM_NOT_NULL_DEBUG(in);
            auto ret { side<Out>(in) }; // Not const for possible move ret
            affirm<Err>(full(ret), WHOAMI_WITH_SOURCE "Dynamic pointer cast failed");
            return ret;
        }

        /** Return true if the dynamic cast desired will pass; in may not be nullptr
         *  Note: this does not do any static assertion verification itself
         *  Note: This requires the type of exception to be thrown to be passed
         */
        template <typename To, typename Err, typename In, typename... Args>
        constexpr void test_throw_on_fail(const std::shared_ptr<In> &in, const Args &...args) {
            UTILS_AFFIRM_NOT_NULL_DEBUG(in);
            affirm<Err>(test<To>(in), args...);
        }
    } // namespace Dynamic

    namespace Static {

        /** An up cast */
        template <typename Out, typename In>
        constexpr auto up(const std::shared_ptr<In> &in) noexcept {
            static_assert(is_ancestor<Out, In>, "up_cast passed invalid <In, Out> type pair");
            return Utils::Private::static_pointer_cast<Out>(in); // Does its own checks as well
        }

        /** An static down cast
         *  Is dynamic and throws on failure during debugging
         */
        template <typename Out, typename In>
        constexpr auto down(const std::shared_ptr<In> &in)
#ifdef DEBUG
        {
            return Utils::Cast::Dynamic::down<Out>(in);
        }
#else
            noexcept {
            static_assert(is_ancestor<In, Out>,
                          "static_down_cast passed invalid <In, Out> type pair");
            return Utils::Private::static_side_cast<Out>(in); // Does its own checks as well
        }
#endif

        /** An static side cast
         *  Is dynamic and throws on failure during debugging
         */
        template <typename Out, typename In>
        constexpr auto side(const std::shared_ptr<In> &in)
#ifdef DEBUG
        {
            return Utils::Cast::Dynamic::side<Out>(in);
        }
#else
            noexcept {
            return Utils::Private::static_side_cast<Out>(in);
        }
#endif

        /** Cast from void; in may not be nullptr
         *  In may be a const qualifed void type
         *  Note: this does not do any verification
         */
        template <typename Out, typename In>
        constexpr auto from_void(const std::shared_ptr<In> &in) {
            UTILS_AFFIRM_NOT_NULL_DEBUG(in);
            static_assert(Utils::is_in_ignore_const<In, void>, "Will only cast from void type");
            static_assert(!Utils::is_same_ignore_cv<Out, void>, "Cannot cast to void");
            return Utils::Private::static_pointer_cast<Out>(in);
        }
    } // namespace Static

} // namespace Utils::Cast

#endif
