/** @file */
#include "cout.hpp"

#include <iostream>


// For brevity
using namespace Utils::Log::Backend;

Cout::Cout() : OStream(std::cout) {}
