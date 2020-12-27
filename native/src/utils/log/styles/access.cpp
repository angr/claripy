/** @file */
#include "access.hpp"

#include "abstract_base.hpp"
#include "default.hpp"

#include "../../thread_safe_access.hpp"


// For brevity
using namespace Utils;
using namespace Log;
using Sty = Style::AbstractBase;


// File local variables
static ThreadSafeAccess<Sty> access(std::make_shared<Style::Default>());
using Ptr = decltype(access)::Ptr;


void Style::Private::set(Ptr &ptr) {
    access.set_shared_ptr(ptr);
}

Ptr Style::get() {
    return access.get();
}
