/** @file */
#include "ostream.hpp"


// For brevity
using namespace Utils::Log::Backend;


OStream::OStream(std::ostream &s) : stream(s) {}


void OStream::log(Constants::CCSC id, const Level::Level &lvl, const std::string &msg) {
    this->stream << msg << std::endl;
    (void) id;
    (void) lvl;
}
