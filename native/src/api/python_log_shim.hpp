/**
 * @file
 * \ingroup util
 * @brief This file defines the python logging backend
 */
#ifndef R_API_PYTHONLOGSHIM_HPP_
#define R_API_PYTHONLOGSHIM_HPP_

#include "cpp.hpp"

#include "../util.hpp"


// Static checks
static_assert(ClaricppLogLvlDebug == 10, "Does not match python Debug value");    // NOLINT
static_assert(ClaricppLogLvlInfo == 20, "Does not match python Debug value");     // NOLINT
static_assert(ClaricppLogLvlWarning == 30, "Does not match python Debug value");  // NOLINT
static_assert(ClaricppLogLvlError == 40, "Does not match python Debug value");    // NOLINT
static_assert(ClaricppLogLvlCritical == 50, "Does not match python Debug value"); // NOLINT


namespace API {

    /** The python log backend; forwards logs to python */
    struct PythonLogShim final : public Util::Log::Backend::Multiplexable {
        /** An alias for log level */
        using Lvl = Util::Log::Level::Level;

        /** Backend name */
        inline CCSC name() const noexcept final { return "PythonLogShim"; }

        /** Constructor */
        inline PythonLogShim(ClaricppPyLog plog, ClaricppPyLevel plvl) noexcept
            : py_log { plog }, py_lvl { plvl } {}

        /** Destructor */
        inline ~PythonLogShim() noexcept = default;

        /** Log the given message */
        inline void log(CCSC id, const Lvl &lvl, Util::LazyStr &&msg) const final {
            log_body(id, lvl, std::move(msg));
        }

        /** Log the given string message */
        inline void log_str(CCSC id, const Lvl &lvl, std::string &&msg) const final {
            log_body(id, lvl, std::move(msg));
        }

        /** Flush is a no-op here @todo: should it be? */
        inline void flush() const final {}

      private:
        /** Helper log function */
        template <typename T> inline void log_body(CCSC id, const Lvl &lvl, T &&msg) const {
            UTIL_CCBOOL is_lazy { std::is_same_v<T, Util::LazyStr> };
            static_assert(std::is_same_v<T, std::string> || is_lazy, "Unexpected choice of T");
            const auto c_lvl { API::mode(lvl) };
            if (c_lvl >= py_lvl(id)) { // Technically a data race here
                if constexpr (is_lazy) {
                    py_log(id, c_lvl, msg().c_str()); // Lazy
                }
                else {
                    py_log(id, c_lvl, msg.c_str()); // std::string
                }
            }
        }

        /** The python log function */
        ClaricppPyLog py_log;
        /** The python level getter function */
        ClaricppPyLevel py_lvl;
    };

} // namespace API

#endif
