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
static ThreadSafe::Access<const Sty> access_ {
    make_derived_shared<const Sty, const Style::Default>()
};


void Style::silent_less_safe_set(std::shared_ptr<const Base> &&ptr) {
    UTIL_ASSERT_NOT_NULL_DEBUG(ptr);
    access_.set_shared_ptr_move(std::move(ptr));
}

void Style::less_safe_set(std::shared_ptr<const Base> &&ptr) {
    UTIL_ASSERT_NOT_NULL_DEBUG(ptr);
    info("Replacing log style \"", get()->name(), "\" with log style \"", ptr->name(), '"');
    access_.set_shared_ptr_move(std::move(ptr));
    info("Log style successfully installed!");
}

std::shared_ptr<const Style::Base> Style::get() {
    return access_.get();
}
