/** @file
 * \ingroup util
 */
#include "generators.hpp"

#include "../assert.hpp"
#include "../demangle.hpp"
#include "../min.hpp"
#include "../safe_alloc.hpp"
#include "../to_hex.hpp"
#include "../widen.hpp"

#include <cmath>
#include <dlfcn.h>
#include <execinfo.h>
#include <iomanip>
#include <sstream>


// Enabling this requires linking to dl
#if 0

/** A private helper function used to print a backtrace line */
static void print_bt_line(std::ostream &o, const int lg_i, const U64 line_num, const U64 addr,
                          CCSC mangled, const std::uintptr_t offset) {
    const constexpr unsigned ptr_width { 2 + 2 * sizeof(void *) };
    o << std::setw(lg_i) << std::left << line_num << " : " << std::setw(ptr_width) << std::left
      << Util::to_hex(addr) << " : " << Util::try_demangle(mangled) << " + " << offset << '\n';
}

/** A private helper function used to print a backtrace line */
static void print_raw_bt_line(std::ostream &o, const int lg_i, const U64 line_num, CCSC line) {
    o << std::setw(lg_i) << std::left << line_num << " : " << line << '\n';
}

/** Save a backtrace to o */
inline void Util::Backtrace::native(std::ostream &o, const unsigned ignore_frames,
                                    const int16_t max_frames) noexcept {
    #ifdef DEBUG
    // Prevent infinite recursion if something goes wrong
    const auto old { Util::Err::Claricpp::toggle_backtrace(false) };
    #endif
    o << "Backtrace:\n";
    // Dummy variables
    int _ignore_int;   // NOLINT
    char _ignore_char; // NOLINT
    std::string _ignore_str;
    // String parsing variables
    std::string sym;
    // The call stack
    void **callstack { nullptr };
    // Try to get a back trace
    try {
        namespace Err = Util::Err;
        UTIL_ASSERT(Err::Usage, max_frames > 0, "max_frames must be strictly positive");
        // Get a human read-able call stack
        callstack = Util::Safe::malloc<void *>(Util::widen<uint32_t, true>(max_frames));
        const int n_frames { ::backtrace(callstack, max_frames) };
        UTIL_ASSERT(Err::Unknown, n_frames > 0, "backtrace failed");
        UTIL_ASSERT(Err::Unknown, n_frames <= max_frames, "backtrace overflow failure");
        CCSC *const symbols { ::backtrace_symbols(callstack, n_frames) };
        // Used for formatting
        const auto n_to_print { Util::widen<U64, true>(
            Util::Min::value(n_frames, 1 + static_cast<int>(max_frames))) };
        const auto lg_i { static_cast<int>(std::ceil(std::log10(n_to_print))) };
        // Print stack
        Dl_info data { nullptr, nullptr, nullptr, nullptr };

        for (U64 i { static_cast<U64>(ignore_frames) + 1 }; i < n_to_print; ++i) {
            const bool matched { ::dladdr(callstack[i], &data) != 0 }; // NOLINT
            // Check to see if we can resolve the symbol name
            if (matched && data.dli_sname != nullptr) {
                const uintptr_t cs_addr { reinterpret_cast<uintptr_t>(callstack[i]) }; // NOLINT
                const uintptr_t dl_addr { reinterpret_cast<uintptr_t>(data.dli_saddr) };
                print_bt_line(o, lg_i, i, cs_addr, data.dli_sname, cs_addr - dl_addr); // NOLINT
            }
            // Name not found
            else {
                U64 addr;              // NOLINT
                std::uintptr_t offset; // NOLINT
                // Try to parse the line
                std::istringstream line { symbols[i] }; // NOLINT
                if (line >> _ignore_int >> _ignore_str >> std::hex >> addr >> sym >> _ignore_char >>
                    std::dec >> offset) {
                    print_bt_line(o, lg_i, i, addr, sym.c_str(), offset);
                }
                // Parse failed
                else {
                    print_raw_bt_line(o, lg_i, i, symbols[i]); // NOLINT
                }
            }
        }
    }
    catch (std::exception &e) {
        o << "Failed with std::exception: " << e.what() << '\n';
    }
    // Cleanup
    std::free(callstack); // NOLINT
    #ifdef DEBUG
    Util::Err::Claricpp::toggle_backtrace(old);
    #endif
}

#endif