/** @file */
#include "multiplex.hpp"


// For brevity
using namespace Utils::Log::Backend;


void Multiplex::log(Constants::CCSC id, const Level::Level &lvl, const std::string &msg) {
    using CItr = decltype(this->cbegin());
    for (CItr i = this->cbegin(); i != this->cend(); ++i) {
        (*i)->log(id, lvl, msg);
    }
}
