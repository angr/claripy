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
using Sty = Style::Base;


// File local variables
static ThreadSafe::Access<const Sty> access {
    make_derived_shared<const Sty, const Style::Default>()
};


void Style::unsafe_set(std::shared_ptr<const Base> &&ptr, const bool silent) {
    UTIL_ASSERT_NOT_NULL_DEBUG(ptr);
    if (!silent) {
        info("Replacing log style \"", get()->name(), "\" with log style \"", ptr->name(), '"');
    }
    access.set_shared_ptr_move(std::move(ptr));
    if (!silent) {
        info("Log style successfully installed!");
    }
}

std::shared_ptr<const Style::Base> Style::get() {
    return access.get();
}
