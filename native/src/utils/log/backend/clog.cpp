/**
 * @file
 * \ingroup utils
 */
#include "clog.hpp"

#include <iostream>


// For brevity
using namespace Utils::Log::Backend;


Clog::Clog() : OStream(std::clog, false) {}
