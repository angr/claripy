/**
 * @file
 * \ingroup utils
 */
#include "multiplex.hpp"


// For brevity
using namespace Utils::Log::Backend;


void Multiplex::log(Constants::CCSC id, const Level::Level &lvl, const std::string &msg) {
    for (const auto &i : *backends.get()) {
        i->log(id, lvl, msg);
    }
}
