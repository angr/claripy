/** @file */
#include "errors.hpp"

#include <cstring>


// For clarity
using namespace Errors;

AST::AST(const char *const what) : msg(what) {}

const char *AST::what() const throw() {
    return msg.c_str();
}
