/**
 * @file
 * \ingroup util
 * @brief This file defines an alternative to Util::Log::error and Util::Log::critical
 * This will log to standard error and should be used extremely sparingly and only Log cannot
 */
#ifndef R_UTIL_FALLBACKERRORLOG_HPP_
#define R_UTIL_FALLBACKERRORLOG_HPP_

#include "../macros.hpp"

#include <cstdio>


/** A macro used to start create a fallback log (populates things like line number etc)
 *  Pass the result of this to fallbaack_error_log as the first argument
 *  MSG should be the first char * desired to log; additional messages can be added via .log()
 */
#define UTIL_NEW_FALLBACK_ERROR_LOG(MSG)                                                           \
    (::Util::FallbackLog { __FILE__, __LINE__, __func__, __BASE_FILE__, (MSG) })

namespace Util {

    /** A private struct a user should not create used for the fallback error log
     *  Use UTIL_NEW_FALLBACK_ERROR_LOG to construct this
     */
    class FallbackLog final {
      public:
        /** A constructor; Note: UTIL_NEW_FALLBACK_ERROR_LOG should be called instead */
        explicit inline FallbackLog(CCSC fl, const U64 ln, CCSC fn, CCSC bf, CCSC msg) noexcept
            : fp { stderr } {
            log("\n**************************"
                "\n*** Fallback Log Start ***"
                "\n**************************\n");
            std::fprintf(fp, "From %s: %llu (%s) via %s\n\n", fl, ln, fn, bf);
            log(msg); // Flushes buffer
        }

        /** Destructor */
        inline ~FallbackLog() noexcept {
            log("\n"
                "\n************************"
                "\n*** Fallback Log End ***"
                "\n************************\n");
        }

        /** Logs what */
        inline FallbackLog &log(CCSC what) noexcept {
            std::fprintf(fp, "%s", what);
            std::fflush(fp);
            return *this;
        }

      private:
        SET_IMPLICITS_EXCLUDE_DEFAULT_CTOR(FallbackLog, delete);
        /** The stream to write to */
        FILE *const fp;
    };

} // namespace Util

#endif
