/**
 * @file
 * \ingroup utils
 */
#include "claricpp.hpp"


// For clarity
using namespace Utils::Error;


Claricpp::~Claricpp() noexcept = default;

const char *Claricpp::what() const noexcept {
    return msg.c_str();
}
