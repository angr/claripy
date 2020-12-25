/** @file */
#include "ostream.hpp"


// For brevity
using namespace Utils::Log::Backend;


OStream::OStream(const std::ostream &s) : stream(s.rdbuf()) {}


void OStream::log(Constants::CCSC id, const Level &lvl, const std::string &msg) {
    this->stream << msg << std::endl;
    (void) id;
    (void) lvl;
}
