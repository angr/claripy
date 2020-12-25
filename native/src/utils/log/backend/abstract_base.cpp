/** @file */
#include "abstract_base.hpp"

#include "../../../errors/unexpected.hpp"

// For brevity
using namespace Utils::Log::Backend;


AbstractBase::AbstractBase() {}

// Disallow usage
std::string AbstractBase::operator()(Constants::CCSC, const Level &, const std::string &) const {
    throw Errors::Unexpected::IncorrectUsage("This function should not be possible to call");
}
