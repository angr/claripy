/**
 * @file
 * \ingroup util
 */
#include "backward.hpp"

#include <backward.hpp>


void Util::Backtrace::backward(std::ostream &o, const UInt ignore_frames,
                               const int16_t max_frames) noexcept {
    namespace B = backward;
    // Backtrace
    B::StackTrace st;
    st.load_here(static_cast<std::size_t>(max_frames));
    st.skip_n_firsts(ignore_frames);
    // Config printer
    B::Printer p;
    p.snippet = true;
    p.object = true;
    p.address = true;
    p.color_mode =
#ifdef ENABLE_ANSI_COLOR_CODES
        B::ColorMode::always;
#else
        B::ColorMode::automatic;
#endif
    // Output
    p.print(st, o);
}
