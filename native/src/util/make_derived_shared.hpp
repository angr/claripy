/**
 * @file
 * \ingroup util
 * @brief This file defines a function to make a shared_ptr<Base> of of a Derived
 * These casts preserve the const-ness of the internal type
 */
#ifndef R_SRC_UTIL_MAKEDERIVEDSHARED_HPP_
#define R_SRC_UTIL_MAKEDERIVEDSHARED_HPP_

#include "pointer_cast.hpp"
#include "type.hpp"

#include <memory>
#include <type_traits>


namespace Util {

    /** Make an std::shared_ptr<Base> from a Derived with args Args
     *  Note: If Base is const, a const Derived is made
     */
    template <typename Base, typename Derived, typename... Args>
    inline std::shared_ptr<Base> make_derived_shared(Args &&...args) {
        // Static verification
        static_assert(Type::Is::ancestor<Base, Derived>, "Derived must derive from Base");
        if constexpr (std::is_const_v<Derived>) {
            static_assert(std::is_const_v<Base>, "Derived is const, so Base must also be const");
        }
        // Transfer const-ness
        using TrueDerived = Type::TransferConst<Derived, Base>;
        if constexpr (Type::Is::same_ignore_const<Base, Derived>) {
            return std::make_shared<TrueDerived>(std::forward<Args>(args)...);
        }
        else {
            // Return initialize a static up cast from a new Derived constructed via forwarded args
            return PCast::Static::up<Base>(
                std::make_shared<TrueDerived>(std::forward<Args>(args)...));
        }
    }

} // namespace Util

#endif
