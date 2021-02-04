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
using Sty = Style::Base;


// File local variables
static ThreadSafeAccess<const Sty> access(std::make_shared<const Style::Default>());
using Ptr = decltype(access)::Ptr;


void Style::Private::set(Ptr &&ptr) {
    access.set_shared_ptr_move(std::forward<Ptr>(ptr));
}

Ptr Style::get() {
    return access.get();
}
