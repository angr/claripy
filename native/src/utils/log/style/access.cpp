/**
 * @file
 * \ingroup utils
 */
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
using Ptr = std::shared_ptr<Style::AbstractBase>;


// Error checking
static_assert(std::is_same_v<Ptr, decltype(access)::Ptr>, "Inconsistiency between pointer types");


void Style::Private::set(Ptr &ptr) {
    access.set_shared_ptr(ptr);
}

Ptr Style::get() {
    return access.get();
}
