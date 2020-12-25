/** @file */
#include "ostream.hpp"


// For brevity
using namespace Utils::Log::Backend;


OStream::OStream(const std::ostream &s) : stream(s.rdbuf()) {}


void OStream::operator()(Constants::CCSC id, const Level &lvl, const std::string &msg) const {
    (void) id;
    (void) lvl;
    (void) msg;
}
