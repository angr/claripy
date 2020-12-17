/** @file */
#include "claricpp.hpp"

#include <cstring>


// For clarity
using namespace Errors;

Claricpp::Claricpp() {}

Claricpp::Claricpp(const Claricpp &o) {
    this->msg = o.msg;
}

Claricpp::Claricpp(Claricpp &&o) {
    this->msg = std::move(o.msg);
}

const char *Claricpp::what() const throw() {
    return msg.c_str();
}
