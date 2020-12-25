/** @file */
#include "access.hpp"

#include "abstract_base.hpp"
#include "default.hpp"

#include <memory>
#include <shared_mutex>

// For brevity
using namespace Utils::Log;
using Bk = Backend::AbstractBase;


// File local variables
static std::shared_mutex style_lock;
static std::shared_ptr<Bk> backend(new Backend::Default());


void Backend::Private::set(std::shared_ptr<Bk> &&b) {
    std::unique_lock<decltype(style_lock)> l(style_lock);
    backend = b;
}

std::shared_ptr<Bk> Backend::get() {
    std::shared_lock<decltype(style_lock)> l(style_lock);
    return backend;
}
