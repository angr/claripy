/**
 * @file
 * \ingroup util
 * @brief This file defines map_set
 */
#ifndef R_SRC_UTIL_MAPADD_HPP_
#define R_SRC_UTIL_MAPADD_HPP_

#include <map>


namespace Util {

    namespace Private {
        /** Quickly put Key, Value{foward(args)...} into map
         *  If ErrIfEmplaceFails an error will be raised if emplacement fails
         *  Note: This assumes the map type has a Key type that is Key with no const or reference
         */
        template <bool ErrIfEmplaceFails, typename Key, typename Value, typename... Args>
        auto map_add(std::map<std::remove_cv_t<std::remove_reference_t<Key>>, Value> &map,
                     Key &&key, Args &&...args) {
            constexpr const bool val_const { std::is_const_v<Value> };
            static_assert(!val_const || ErrIfEmplaceFails,
                          "ErrIfEmplaceFails must be true for maps with constant value types");
            // First try emplacing.
            // Normally this forward would plunder args, but try_emplace will only plunder if the
            // item doesn't already exist, so if success is false we should be able to use args
            // again
            const auto [iter, success] { map.try_emplace(std::forward<Key>(key),
                                                         std::forward<Args...>(args)...) };
            if (!success) {
                // This is an if instead of just an affirm because this must not be compiled if
                // false
                if constexpr (!val_const && !ErrIfEmplaceFails) {
                    iter->second = std::move(Value { std::forward<Args...>(args)... });
                }
                else {
                    UTIL_THROW(Util::Err::Collision,
                               "Key collision during addition to map with const value type");
                }
            }
            return iter;
        }
    } // namespace Private

    /** Quickly put Key, Value{foward(args)...} into map
     *  Note: This assumes the map type has a Key type that is Key with no const or reference
     *  Note: value type may not be const for this specialization
     */
    template <typename Key, typename Value, typename... Args>
    auto map_set(std::map<std::remove_cv_t<std::remove_reference_t<Key>>, Value> &map, Key &&key,
                 Args &&...args) {
        return Private::map_add<false>(map, std::forward<Key>(key), std::forward<Args>(args)...);
    }

    /** Quickly put Key, Value{forward(args)...} into map
     *  Note: This assumes the map type has a Key type that is Key with no const or reference
     *  Note: If emplacement fails, this function throws an exception
     */
    template <typename Key, typename Value, typename... Args>
    auto map_emplace(std::map<std::remove_cv_t<std::remove_reference_t<Key>>, Value> &map,
                     Key &&key, Args &&...args) {
        return Private::map_add<true>(map, std::forward<Key>(key), std::forward<Args>(args)...);
    }

} // namespace Util

#endif
