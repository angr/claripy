/** @file */
#include "z3.hpp"

namespace Backend::Z3 {

    // Initialize TLS
    thread_local Z3::TLS Z3::tls {};

#ifdef DEBUG
    std::atomic_bool Z3::main_set { false };
#endif

} // namespace Backend::Z3