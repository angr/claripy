/**
 * @file
 * \ingroup utils
 */
#include "ostream.hpp"

#include <memory>
#include <mutex>
#include <ostream>


// For brevity
using namespace Utils::Log::Backend;


OStream::OStream(std::shared_ptr<std::ostream> s, const bool f, const bool f_exit)
    : stream(std::move(s)), flush(f), flush_on_exit(f_exit) {}

OStream::~OStream() {
    if (this->flush_on_exit) {
        this->stream->flush();
    }
}

void OStream::log(Constants::CCSC id, const Level::Level &lvl, const std::string &msg) {
    std::lock_guard<decltype(this->m)> lock(m);
    *stream << msg << "\n";
    if (this->flush) {
        this->stream->flush();
    }
    (void) lvl;
    (void) id;
}
