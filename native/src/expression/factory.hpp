/**
 * @file
 * @brief This file defines Expression factory functions
 */
#ifndef R_EXPRESSION_FACTORY_HPP_
#define R_EXPRESSION_FACTORY_HPP_

#include "base.hpp"

#include "../hash.hpp"
#include "../utils.hpp"


namespace Expression {

    /** A factory used to construct Expression::Base subclasses
     *  Arguments are passed by non-const forwarding reference
     *  @todo update eager_backends functionality
     */
    template <typename T, typename... Args> inline BasePtr factory(Args &&...args) {
        static_assert(Utils::is_ancestor<Base, T>, "T must derive from Expression::Base");
        return ::Factory::factory<Base, T>(std::forward<Args>(args)...);
    }

    /** Get a shared pointer from a hash
     *  If the object does not exist it returns a shared pointer to nullptr
     */
    inline Factory::Ptr<Base> find(const Hash::Hash h) { return ::Factory::find<Base>(h); }

} // namespace Expression

#endif
