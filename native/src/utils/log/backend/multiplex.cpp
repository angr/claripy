/** @file */
#include "multiplex.hpp"


// For brevity
using namespace Utils::Log::Backend;


void Multiplex::log(Constants::CCSC id, const Level::Level &lvl, const std::string &msg) {
    const auto size = this->size();
    const auto data = this->data();
    for (Constants::UInt i = 0; i < size; ++i) {
        data[i]->log(id, lvl, msg);
    }
}
