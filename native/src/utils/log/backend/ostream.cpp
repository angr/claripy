/**
 * @file
 * \ingroup utils
 */
#include "ostream.hpp"

#include <mutex>


// For brevity
using namespace Utils::Log::Backend;


OStream::OStream(std::ostream &s, const bool f) : stream(s), flush(f) {}


void OStream::log(Constants::CCSC id, const Level::Level &lvl, const std::string &msg) {
    std::lock_guard<decltype(this->m)> lock(m);
    this->stream << msg << "\n";
    if (this->flush) {
        std::flush(stream);
    }
    (void) lvl;
    (void) id;
}
