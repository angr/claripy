/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"
#include "utils.hpp"

#include <iostream>


using namespace Utils::Log;
using namespace UnitTest::TestLib;


/** Create a backend class */
struct Cout : Backend::OStream {
    Cout() : Backend::OStream(std::cout) {}
};

/** Verify our set backend was indeed set */
int backend_access() {
    Backend::set<Cout>();
    UNITTEST_ASSERT(dynamic_cast<Cout *>(Backend::get().get()) != nullptr)
    return 0;
}
