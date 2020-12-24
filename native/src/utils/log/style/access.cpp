/** @file */
#include "access.hpp"

#include "default.hpp"

#include <shared_mutex>

// For brevity
using namespace Utils::Log;
// Required since Style::Style can reference constructor in setter parameters
using Sty = Style::Style;


// File local variables
static std::shared_mutex style_lock;
static Style::Style style = Style::Default();
;

void Style::set(Sty s) {
    std::unique_lock<decltype(style_lock)> l(style_lock);
    style = s;
}

Sty Style::get() {
    std::shared_lock<decltype(style_lock)> l(style_lock);
    return style;
}
