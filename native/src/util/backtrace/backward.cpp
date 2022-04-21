/**
 * @file
 * \ingroup util
 */
#include "generators.hpp"
#include "handle_signals.hpp"

#include "../do_once.hpp"
#include "../fallback_error_log.hpp"
#include "../log.hpp"

#include <backward.hpp>
#include <memory>


/** Add a source root for backward */
[[maybe_unused]] static void add_source_root(CCSC native) noexcept {
    try {
        backward::SourceFile::add_paths_to_env_variable_impl(native);
    }
    catch (std::exception &e) {
        UTIL_NEW_FALLBACK_ERROR_LOG("Failed to set backward source root because: ", e.what());
    }
    catch (...) {
        UTIL_NEW_FALLBACK_ERROR_LOG("Failed to set backward source root due "
                                    "to an unknown non-exception being thrown");
    }
}

void Util::Backtrace::backward(std::ostream &o, const unsigned ignore_frames,
                               const int16_t max_frames) noexcept {
#ifdef SOURCE_ROOT_FOR_BACKTRACE
    // This function is threadsafe, no need to ensure it is called exactly once between threads
    // Additional calls to this function don't cause much overhead, so no need for extra sync
    UTIL_ATOMIC_DOONCE(add_source_root(SOURCE_ROOT_FOR_BACKTRACE));
#endif
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
        ::backward::ColorMode::automatic;
#endif
    // Output
    p.print(st, o);
}

void Util::Backtrace::backward_handle_signals() {
    static std::unique_ptr<backward::SignalHandling> sh { nullptr };
    static std::atomic_bool installed { false };
    if (not installed.exchange(true)) {
        Util::Log::debug("Installing backward signal handler");
        sh = std::make_unique<backward::SignalHandling>();
        Util::Log::info("Signal handler installed.");
    }
    else {
        Util::Log::warning("This function has been called before. Doing nothing");
    }
}