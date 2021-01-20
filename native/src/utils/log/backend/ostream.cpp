/**
 * @file
 * \ingroup utils
 */
#include "ostream.hpp"


// For brevity
using namespace Utils::Log::Backend;


OStream::OStream(std::ostream &s, const bool f) : stream(s), flush(f), m() {}


void OStream::log(Constants::CCSC id, const Level::Level &lvl, const std::string &msg) {
    std::unique_lock<decltype(this->m)> lock(m);
    this->stream << msg << "\n";
    if (this->flush) {
        std::flush(stream);
    }
    (void) lvl;
    (void) id;
}
