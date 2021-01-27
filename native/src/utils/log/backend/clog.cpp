/**
 * @file
 * \ingroup utils
 */
#include "clog.hpp"

#include <iostream>
#include <memory>


// For brevity
using namespace Utils::Log::Backend;


Clog::Clog() : OStream(std::make_shared<std::ostream>(std::clog.rdbuf()), false, false) {}
