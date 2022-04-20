/**
 * @file
 * @brief This file defines a quick way to verify that a shared_ptr is pointing to a T
 */
#ifndef R_SRC_CUID_IST_HPP_
#define R_SRC_CUID_IST_HPP_

#include "cuid.hpp"

#include <memory>


namespace CUID {

    /** Return true if x points to a T
     *  x may not be nullptr
     *  Verifies that the static type of what x is pointing to is a superclass of T
     */
    template <typename T, bool AllowKin, typename Base> constexpr bool is_t(CTSC<Base> x) {
        static_assert(Util::Type::Is::ancestor<HasCUID, Base>, "Base must subclass HasCUID");
        static_assert(Util::Type::Is::ancestor<Base, T>, "T must subclass Base");
        UTIL_ASSERT_NOT_NULL_DEBUG(x);
        if constexpr (std::is_final_v<T>) {
            return x->cuid == T::static_cuid; // NOLINT (*null possible in release mode)
        }
        else if constexpr (AllowKin) {
            return Util::PCast::Dynamic::test<T>(x);
        }
        else {
            return false;
        }
    }

    /** Return true if x points to a T
     *  x may not be nullptr
     *  Verifies that the static type of what x is pointing to is a superclass of T
     */
    template <typename T, bool AllowKin, typename Base>
    constexpr bool is_t(const std::shared_ptr<Base> &x) {
        return is_t<T, AllowKin, Base>(x.get());
    }

    /** Return true if x is a T */
    template <typename T, typename Base> bool is_t(CTSC<Base> x) {
        static_assert(std::is_final_v<T>,
                      "is_t only allowed without AllowKin defined if T is final");
        return is_t<T, false, Base>(x);
    }

    /** Return true if x is a T */
    template <typename T, typename Base> bool is_t(const std::shared_ptr<Base> &x) {
        return is_t<T, false, Base>(x.get());
    }

    namespace Private {
        /** Return true if x is a Next or in Allowed */
        template <typename Base, bool AllowKin, typename Next, typename... Allowed>
        bool is_any(const std::shared_ptr<Base> &x) {
            if constexpr (sizeof...(Allowed) > 0) {
                return is_t<Next, AllowKin, Base>(x) || is_any<Base, AllowKin, Allowed...>(x);
            }
            return is_t<Next, AllowKin>(x);
        }
    } // namespace Private

    /** Return true if x is in TS */
    template <typename Base, bool AllowKin, typename Next, typename... Allowed>
    bool is_any_t(const std::shared_ptr<Base> &x) {
        return Private::is_any<Base, AllowKin, Next, Allowed...>(x);
    }

    /** Return true if x is a Next or in Allowed */
    template <typename Base, typename Next, typename... Allowed>
    bool is_any_t(const std::shared_ptr<Base> &x) {
        return is_any_t<Base, false, Next, Allowed...>(x);
    }

} // namespace CUID

#endif
