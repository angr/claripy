/**
 * @file
 * \ingroup utils
 */
#include "cerr.hpp"

#include <iostream>


// For brevity
using namespace Utils::Log::Backend;


Cerr::Cerr() : OStream(std::cerr, true) {}
