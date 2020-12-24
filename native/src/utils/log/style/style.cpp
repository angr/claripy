/** @file */
#include "style.hpp"

#include "../../../errors/unexpected.hpp"

// For brevity
using namespace Utils::Log::Style;


Style::Style() {}

// Disallow usage
std::string Style::operator()(const Level &, std::ostringstream &) const {
    throw Errors::Unexpected::IncorrectUsage("This function should not be possible to call");
}
