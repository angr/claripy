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
static ThreadSafeAccess<const Bk> access(std::make_shared<const Backend::Default>());
using Ptr = decltype(access)::Ptr;


void Backend::Private::set(Ptr &&ptr) {
    access.set_shared_ptr_move(std::forward<Ptr>(ptr));
}

Ptr Backend::get() {
    return access.get();
}
