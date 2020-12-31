/** @file */
#include "claricpp.hpp"

#include <cstring>


// For clarity
using namespace Utils::Error;


const char *Claricpp::what() const throw() {
    return msg.c_str();
}
