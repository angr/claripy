/**
 * @file
 * @brief This file defines a quick way to verify that a shared_ptr is pointing to a T
 */
#ifndef R_CUID_IST_HPP_
#define R_CUID_IST_HPP_

#include "cuid.hpp"

#include <memory>


namespace CUID {

    /** Return true if x points to a T
     *  x may not be nullptr
     *  Verifies that the static type of what x is pointing to is a superclass of T
     */
    template <typename T, bool AllowKin, typename Base>
    constexpr bool is_t(const std::shared_ptr<Base> &x) {
        static_assert(Utils::is_ancestor<HasCUID, Base>, "Base must subclass HasCUID");
        static_assert(Utils::is_ancestor<Base, T>, "T must subclass Base");
        UTILS_AFFIRM_NOT_NULL_DEBUG(x);
        if constexpr (std::is_final_v<T>) {
            return x->cuid == T::static_cuid;
        }
        else if constexpr (AllowKin) {
            return Utils::Cast::Dynamic::test<T>(x);
        }
        else {
            return false;
        }
    }

    /** Return true if x is a T */
    template <typename T, typename Base> bool is_t(const std::shared_ptr<Base> &x) {
        static_assert(std::is_final_v<T>,
                      "is_t only allowed without AllowKin defined if T is final");
        return is_t<T, false, Base>(x);
    }

} // namespace CUID

#endif
