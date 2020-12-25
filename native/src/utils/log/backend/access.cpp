/** @file */
#include "access.hpp"

#include "abstract_base.hpp"
#include "default.hpp"

#include <shared_mutex>

// For brevity
using namespace Utils::Log;
using Bk = Backend::AbstractBase;


// File local variables
static std::shared_mutex style_lock;
static Backend::AbstractBase backend = Backend::Default();
;

void Backend::set(Bk b) {
    std::unique_lock<decltype(style_lock)> l(style_lock);
    backend = b;
}

Bk Backend::get() {
    std::shared_lock<decltype(style_lock)> l(style_lock);
    return backend;
}
