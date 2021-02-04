/**
 * @file
 * \ingroup utils
 */
#include "access.hpp"

#include "base.hpp"
#include "default.hpp"

#include "../../thread_safe_access.hpp"


// For brevity
using namespace Utils;
using namespace Log;
using Bk = Backend::Base;


// Create a thread safe backend wrapper
static ThreadSafeAccess<Bk> access(std::make_shared<Backend::Default>());
using Ptr = std::shared_ptr<Backend::Base>;


// Error checking
static_assert(std::is_same_v<Ptr, decltype(access)::Ptr>, "Inconsistiency between pointer types");


void Backend::Private::set(Ptr &&ptr) {
    access.set_shared_ptr_move(std::forward<Ptr>(ptr));
}

Ptr Backend::get() {
    return access.get();
}
