/** @file */
#include "claricpp.hpp"

#include <cstring>


// For clarity
using namespace Errors;


const char *Claricpp::what() const throw() {
    return msg.c_str();
}
