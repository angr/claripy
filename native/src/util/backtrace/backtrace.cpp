/**
 * @file
 * \ingroup util
 */
#include "backtrace.hpp"

#include "handle_signals.hpp"

#include "../log.hpp"

#include <backward.hpp>
#include <memory>


void Util::Backtrace::add_source_root(CCSC native_dir) {
    static std::mutex m {};
    std::unique_lock<decltype(m)> rw { m };
    backward::SourceFile::add_paths_to_env_variable_impl(native_dir);
    Util::Log::info("Source root added: ", native_dir);
}

void Util::Backtrace::backward(std::ostream &o, const unsigned ignore_frames,
                               const int16_t max_frames) noexcept {
    // Backtrace
    ::backward::StackTrace st;
    st.load_here(static_cast<std::size_t>(max_frames));
    st.skip_n_firsts(static_cast<U64>(ignore_frames) + 1);
    // Config printer
    ::backward::Printer p;
    p.snippet = true;
    p.object = true;
    p.address = true;
    p.color_mode =
#ifdef ENABLE_ANSI_COLOR_CODES
        ::backward::ColorMode::always;
#else
        //    ::backward::ColorMode::automatic;
        ::backward::ColorMode::never;
#endif
    // Output
    p.print(st, o);
}