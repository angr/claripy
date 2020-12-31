/**
 * @file
 * \ingroup utils
 */
#include "access.hpp"

#include "abstract_base.hpp"
#include "default.hpp"

#include "../../thread_safe_access.hpp"

#include <memory>
#include <shared_mutex>

// For brevity
using namespace Utils;
using namespace Log;
using Bk = Backend::AbstractBase;

// Create a thread safe backend wrapper
static ThreadSafeAccess<Bk> access(std::make_shared<Backend::Default>());
using Ptr = decltype(access)::Ptr;

// Default the backend


void Backend::Private::set(Ptr &ptr) {
    access.set_shared_ptr(ptr);
}

Ptr Backend::get() {
    return access.get();
}
