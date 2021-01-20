/**
 * @file
 * \ingroup utils
 */
#include "claricpp.hpp"


// For clarity
using namespace Utils::Error;


Claricpp::~Claricpp() {}

const char *Claricpp::what() const throw() {
    return msg.c_str();
}
