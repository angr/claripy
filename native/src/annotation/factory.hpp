/**
 * @file
 * @brief This file defines the OP factory
 */
#ifndef R_SRC_ANNOTATION_FACTORY_HPP_
#define R_SRC_ANNOTATION_FACTORY_HPP_

#include "base.hpp"

#include "../factory.hpp"
#include "../util.hpp"

#include <memory>
#include <utility>


namespace Annotation {

    /** A factory used to construct Annotation subclasses
     *  Arguments are passed by non-const forwarding reference
     */
    template <typename T, typename... Args> inline BasePtr factory(Args &&...args) {
        static_assert(Util::Type::Is::ancestor<Base, T>, "T must derive from Annotation::Base");
        return ::Factory::factory<Base, T>(std::forward<Args>(args)...);
    }

} // namespace Annotation

#endif
