/**
 * @file
 * \ingroup utils
 */
#include "access.hpp"

#include "base.hpp"
#include "default.hpp"

#include "../../affirm_not_null_debug.hpp"
#include "../../thread_safe.hpp"


// For brevity
using namespace Utils;
using namespace Log;
using Bk = Backend::Base;


// Create a thread safe backend wrapper
static ThreadSafe::Access<const Bk> access {
    make_derived_shared<const Bk, const Backend::Default>()
};


void Backend::unsafe_set(std::shared_ptr<const Base> &&ptr) {
    UTILS_AFFIRM_NOT_NULL_DEBUG(ptr);
    access.set_shared_ptr_move(std::move(ptr));
}

std::shared_ptr<const Backend::Base> Backend::get() {
    return access.get();
}
