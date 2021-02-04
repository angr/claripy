/**
 * @file
 * @brief This file defines the OP factory
 */
#ifndef __ANNOTATION_FACTORY_HPP__
#define __ANNOTATION_FACTORY_HPP__

#include "base.hpp"

#include "../factory.hpp"
#include "../utils.hpp"

#include <memory>
#include <utility>


namespace Annotation {

    /** A factory used to construct Annotation subclasses
     *  Arguments are passed by non-const forwarding reference
     */
    template <typename T, typename... Args> inline Factory::Ptr<T> factory(Args &&...args) {
        static_assert(std::is_base_of_v<Base, T>, "T must derive from Annotation::Base");
        return ::Factory::factory<Base, T>(std::forward<Args>(args)...);
    }

} // namespace Annotation

#endif
