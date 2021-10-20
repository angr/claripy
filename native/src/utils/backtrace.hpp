/**
 * @file
 * \ingroup utils
 * @brief This file defines a method of backtracing the stack
 */
#ifndef R_UTILS_BACKTRACE_HPP_
#define R_UTILS_BACKTRACE_HPP_

#include "affirm.hpp"
#include "demangle.hpp"
#include "error.hpp"
#include "min.hpp"
#include "safe_alloc.hpp"
#include "to_hex.hpp"
#include "widen.hpp"

#include <cmath>
#include <dlfcn.h>
#include <execinfo.h>
#include <iomanip>
#include <sstream>


namespace Utils {

    namespace Private {

        /** A private helper function used to print a backtrace line */
        inline void print_bt_line(std::ostream &o, const int lg_i, const UInt line_num,
                                  const UInt addr, CCSC mangled, const std::uintptr_t offset) {
            const constexpr unsigned ptr_width { 2 + 2 * sizeof(void *) };
            o << std::setw(lg_i) << std::left << line_num << " : " << std::setw(ptr_width)
              << std::left << to_hex(addr) << " : " << try_demangle(mangled) << " + " << offset
              << '\n';
        }

        /** A private helper function used to print a backtrace line */
        inline void print_raw_bt_line(std::ostream &o, const int lg_i, const UInt line_num,
                                      CCSC line) {
            o << std::setw(lg_i) << std::left << line_num << " : " << line << '\n';
        }

    } // namespace Private

    inline void backtrace(std::ostream &o, const UInt ignore_frames = 0,
                          const int16_t max_frames = 0x1000) noexcept {
#ifdef DEBUG
        // Prevent infinite recursion if something goes wrong
        const auto old { Utils::Error::Claricpp::toggle_backtrace(false) };
#endif
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
            namespace Err = Utils::Error::Unexpected;
            Utils::affirm<Err::Usage>(max_frames > 0, "max_frames must be strictly positive");
            // Get a human read-able call stack
            callstack = Utils::Safe::malloc<void *>(Utils::widen<uint32_t, true>(max_frames));
            const int n_frames { ::backtrace(callstack, max_frames) };
            Utils::affirm<Err::Unknown>(n_frames > 0, WHOAMI_WITH_SOURCE "backtrace failed");
            Utils::affirm<Err::Unknown>(n_frames <= max_frames,
                                        WHOAMI_WITH_SOURCE "backtrace overflow failure");
            CCSC *const symbols { ::backtrace_symbols(callstack, n_frames) };
            // Used for formatting
            const auto n_to_print { Utils::widen<UInt, true>(
                Utils::Min::value(n_frames, 1 + static_cast<int>(max_frames))) };
            const auto lg_i { static_cast<int>(std::ceil(std::log10(n_to_print))) };
            // Print stack
            Dl_info data { nullptr, nullptr, nullptr, nullptr };

            for (UInt i { ignore_frames + 1 }; i < n_to_print; ++i) {      // utils widen
                const bool matched { ::dladdr(callstack[i], &data) != 0 }; // NOLINT
                // Check to see if we can resolve the symbol name
                if (matched && data.dli_sname != nullptr) {
                    const uintptr_t addr { reinterpret_cast<uintptr_t>(callstack[i]) }; // NOLINT
                    const uintptr_t offset { addr - reinterpret_cast<uintptr_t>(
                                                        data.dli_saddr) };            // NOLINT
                    Private::print_bt_line(o, lg_i, i, addr, data.dli_sname, offset); // NOLINT
                }
                // Name not found
                else {
                    UInt addr;             // NOLINT
                    std::uintptr_t offset; // NOLINT
                    // Try to parse the line
                    std::istringstream line { symbols[i] }; // NOLINT
                    if (line >> _ignore_int >> _ignore_str >> std::hex >> addr >> sym >>
                        _ignore_char >> std::dec >> offset) {
                        Private::print_bt_line(o, lg_i, i, addr, sym.c_str(), offset);
                    }
                    // Parse failed
                    else {
                        Private::print_raw_bt_line(o, lg_i, i, symbols[i]); // NOLINT
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
        Utils::Error::Claricpp::toggle_backtrace(old);
#endif
    }

} // namespace Utils

#endif
