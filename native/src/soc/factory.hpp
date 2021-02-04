/**
 * @file
 * @brief This file defines the SOC factory function
 */
#ifndef __SOC_FACTORY_HPP__
#define __SOC_FACTORY_HPP__

#include "../factory.hpp"


namespace SOC {

    // Forward declarations
    struct Base;

    /** A factory used to construct subclasses of SOC.
     *  Arguments are passed by non-const forwarding reference
     */
    template <typename T, typename... Args>
    inline Factory::Ptr<T> factory(Args &&...args) {
        static_assert(std::is_base_of_v<Base, T>, "T must derive from SOC::Base");
        return ::Factory::factory<Base, T>(std::forward<Args>(args)...);
    }

} // namespace SOC

#endif
