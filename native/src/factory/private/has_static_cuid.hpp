/**
 * @file
 * @brief This file defines a method used to determine if a class has a static cuid defined
 */
#ifndef R_SRC_FACTORY_PRIVATE_HASSTATICCUID_HPP_
#define R_SRC_FACTORY_PRIVATE_HASSTATICCUID_HPP_

#include "../../util.hpp"


namespace Factory::Private {

    /** Used to determine if T has a static member called static_cuid
     *  False case
     */
    template <typename T, typename = int> struct HasStaticCUID final : std::false_type {};

    /** Used to determine if T has a static U64 called static_cuid
     *  True case
     *  The comma operator returns the second item, so "(A, B)" returns B
     *  If static_cuid does not exist, T::static_cuid fails is not resolvable so this
     *  specialization is rejected (via SFINAE) in favor if the previous, more general, definition
     *  If static_cuid exists, then (T::static_cuid,  0) returns 0, and we have specialized
     *  with int = 0. Note that specializations are prioritized over the general definition
     */
    template <typename T>
    struct HasStaticCUID<T, decltype((void) T::static_cuid, 0)> final : std::true_type {};

    /** Used to determine of T has a static_cuid variable */
    template <typename T> UTIL_ICCBOOL has_static_cuid = HasStaticCUID<T>::value;

} // namespace Factory::Private

#endif
