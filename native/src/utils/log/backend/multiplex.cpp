/**
 * @file
 * \ingroup utils
 */
#include "multiplex.hpp"


// For brevity
using namespace Utils::Log::Backend;


void Multiplex::log(Constants::CCSC id, const Level::Level &lvl, const std::string &msg) {
	const auto vec = backends.get();
    const auto size = vec->size();
    const auto data = vec->data();
    for (Constants::UInt i = 0; i < size; ++i) {
        data[i]->log(id, lvl, msg);
    }
}
