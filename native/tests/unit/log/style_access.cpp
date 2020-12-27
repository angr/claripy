/** @file */

#include "src/utils.hpp"


using namespace Utils::Log;


/** Create a style class */
struct Plain : Style::AbstractBase {
    /** The style function */
    std::string str(Constants::CCSC, const Level::Level &, const std::ostringstream &s) override {
        return s.str();
    }
};

/** Verify our set style was indeed set */
int style_access() {
    Style::set<Plain>();
    if (dynamic_cast<Plain *>(Style::get().get()) != nullptr) {
        return 0;
    }
    else {
        return 1;
    }
}
