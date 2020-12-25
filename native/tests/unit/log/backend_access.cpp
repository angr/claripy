
/** @file */

#include "src/utils.hpp"

#include <iostream>


using namespace Utils::Log;


/** Create a backend class */
struct Cout : Backend::OStream {
    Cout() : Backend::OStream(std::cout) {}
};

/** Verify our set backend was indeed set */
int backend_access() {
    Backend::set<Cout>();
    if (dynamic_cast<Cout *>(Backend::get().get()) != nullptr) {
        return 0;
    }
    else {
        return 1;
    }
}
