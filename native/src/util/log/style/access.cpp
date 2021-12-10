/**
 * @file
 * \ingroup util
 */
#include "access.hpp"

#include "base.hpp"
#include "default.hpp"

#include "../../assert_not_null_debug.hpp"
#include "../../thread_safe.hpp"


// For brevity
using namespace Util;
using namespace Log;
using Sty = Style::Base;


// File local variables
static ThreadSafe::Access<const Sty> access {
    make_derived_shared<const Sty, const Style::Default>()
};


void Style::unsafe_set(std::shared_ptr<const Base> &&ptr) {
    UTIL_ASSERT_NOT_NULL_DEBUG(ptr);
    access.set_shared_ptr_move(std::move(ptr));
}

std::shared_ptr<const Style::Base> Style::get() {
    return access.get();
}
