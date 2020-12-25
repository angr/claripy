/** @file */
#include "access.hpp"

#include "abstract_base.hpp"
#include "default.hpp"

#include <shared_mutex>

// For brevity
using namespace Utils::Log;
using Sty = Style::AbstractBase;


// File local variables
static std::shared_mutex style_lock;
static std::shared_ptr<Sty> style(new Style::Default());


void Style::Private::set(std::shared_ptr<Sty> &&s) {
    std::unique_lock<decltype(style_lock)> l(style_lock);
    style = s;
}

std::shared_ptr<Sty> Style::get() {
    std::shared_lock<decltype(style_lock)> l(style_lock);
    return style;
}
