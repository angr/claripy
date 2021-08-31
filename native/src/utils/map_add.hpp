/**
 * @file
 * \ingroup utils
 * @brief This file defines map_add
 */
#ifndef R_UTILS_MAPADD_HPP_
#define R_UTILS_MAPADD_HPP_

#include <map>


namespace Utils {

    /** Quickly put Key, Value{foward(args)...} into map
     *  Note: This assumes the map type has a Key type that is Key with no const or reference
     */
    template <typename Key, typename Value, typename... Args>
    auto map_add(std::map<std::remove_cv_t<std::remove_reference_t<Key>>, Value> &map, Key &&key,
                 Args &&...args) {
        // First try emplacing.
        // Normally this forward would plunder args, but try_emplace will only plunder if the
        // item doesn't already exist, so if success is false we should be able to use args again
        const auto [iter, success] { map.try_emplace(std::forward<Key>(key),
                                                     std::forward<Args...>(args)...) };
        if (!success) {
            // This is an if instead of just an affirm because this must not be compiled if false
            if constexpr (!std::is_const_v<Value>) {
                iter->second = std::move(Value { std::forward<Args...>(args)... });
            }
            else {
                throw Utils::Error::Unexpected::Collision(
                    WHOAMI_WITH_SOURCE,
                    "Key collision during addition to map with const value type");
            }
        }
        return iter;
    }

} // namespace Utils

#endif
