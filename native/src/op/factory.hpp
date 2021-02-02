/**
 * @file
 * @brief This file defines the OP factory
 */
#ifndef __OP_FACTORY_HPP__
#define __OP_FACTORY_HPP__

#include "base.hpp"

#include "../factory.hpp"
#include "../hash.hpp"
#include "../utils.hpp"

#include <memory>
#include <utility>


namespace Op {

    /** A factory used to construct Op subclasses
     *  Arguments are passed by non-const forwarding reference
     */
    template <typename T, typename... Args>
    inline Constants::SPtr<const T> factory(Args &&...args) {
        static_assert(std::is_base_of_v<Base, T>, "T must derive from SOC::Base");
        return ::Factory::factory<Base, T>(std::forward<Args>(args)...);
    }

} // namespace Op

#endif
