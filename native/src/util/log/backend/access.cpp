/**
 * @file
 * \ingroup util
 */
#include "../../assert_not_null_debug.hpp"
#include "../../thread_safe.hpp"
#include "../log.hpp"


// For brevity
using namespace Util;
using namespace Log;
using Bk = Backend::Base;


// Create a thread safe backend wrapper
static ThreadSafe::Access<const Bk> access {
    make_derived_shared<const Bk, const Backend::Default>()
};


void Backend::unsafe_set(std::shared_ptr<const Base> &&ptr) {
    UTIL_ASSERT_NOT_NULL_DEBUG(ptr);
    info(WHOAMI "Logging backend about to update");
    access.set_shared_ptr_move(std::move(ptr));
    info(WHOAMI "Logging backend updated");
}

std::shared_ptr<const Backend::Base> Backend::get() {
    return access.get();
}
