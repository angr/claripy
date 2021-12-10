/**
 * @file
 * \ingroup util
 */
#include "stack_limit.hpp"


// For brevity
namespace US = Util::StackLimit;


// Not all systems support this
#if !__has_include(<sys/resource.h>)


/** A helper function which reports that StackLimit operations are not supported on this system */
static void not_supported() {
    UTIL_THROW(Util::Err::NotSupported, "This system does not support StackLimit operations");
}

US::ULL US::get() {
    not_supported();
}
US::ULL US::max() {
    not_supported();
}
void US::set(const US::ULL) {
    not_supported();
}


// Systems that do support this
#else

    #include "assert.hpp"
    #include "err.hpp"
    #include "verify_syscall.hpp"

    #include <cerrno>
    #include <cstring>
    #include <sys/resource.h>


/** A helper function to get the current rlimit struct */
static rlimit getr() {
    rlimit rl {};
    const auto rv { getrlimit(RLIMIT_STACK, &rl) };
    Util::verify_syscall(rv);
    return rl;
}

US::ULL US::get() {
    return getr().rlim_cur;
}

US::ULL US::max() {
    return getr().rlim_max;
}

void US::set(const US::ULL to) {
    auto rl { getr() };
    UTIL_ASSERT(Err::Usage, to <= rl.rlim_max, "selected stack limit of ", to,
                " is greater than the max of: ", rl.rlim_max);
    rl.rlim_cur = to;
    verify_syscall(setrlimit(RLIMIT_STACK, &rl));
}


#endif
