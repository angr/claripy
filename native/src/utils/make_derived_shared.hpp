/**
 * @file
 * \ingroup utils
 * @brief This file defines a function to make a shared_ptr<Base> of of a Derived
 * These casts preserve the constness of the internal type
 */
#ifndef __UTILS_MAKEDERIVEDSHARED_HPP__
#define __UTILS_MAKEDERIVEDSHARED_HPP__

#include "pointer_cast.hpp"
#include "transfer_const.hpp"

#include <memory>
#include <type_traits>


namespace Utils {

    /** Make an std::shared_ptr<Base> from a Derived with args Args
     *  Note: constness of Base is transferred onto Derived
     */
    template <typename Base, typename Derived, typename... Args>
    inline std::shared_ptr<Base> make_derived_shared(Args &&...args) {
        // Transfer constness
        using TrueDerived = TransferConst<Derived, Base>;
        // Static verification
        static_assert(is_ancestor<Base, TrueDerived>, "Derived must derive from Base");
        if constexpr (std::is_same_v<Base, TrueDerived>) {
            return std::make_shared<TrueDerived>(std::forward<Args>(args)...);
        }
        else {
            // Return initialize a static up cast from a new Derived constructed via fowarded args
            return up_cast<Base>(std::make_shared<TrueDerived>(std::forward<Args>(args)...));
        }
    }

} // namespace Utils

#endif
