/**
 * @file
 * \ingroup utils
 */
#include "cerr.hpp"

#include <iostream>
#include <memory>


// For brevity
using namespace Utils::Log::Backend;


Cerr::Cerr() : OStream(std::make_shared<std::ostream>(std::cerr.rdbuf()), true, false) {}
