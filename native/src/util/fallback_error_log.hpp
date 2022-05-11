/**
 * @file
 * \ingroup util
 * @brief This file defines an alternative to Util::Log::error and Util::Log::critical
 * This will log to standard error and should be used extremely sparingly and only Log cannot
 */
#ifndef R_SRC_UTIL_FALLBACKERRORLOG_HPP_
#define R_SRC_UTIL_FALLBACKERRORLOG_HPP_

#include "dependent_constant.hpp"
#include "type.hpp"

#include "../macros.hpp"

#include <cstdio>
#include <exception> // For catch macro


/** A macro used to start create a fallback log (populates things like line number etc)
 *  Pass the result of this to fallbaack_error_log as the first argument
 *  MSG should be the first char * desired to log; additional messages can be added via .log()
 */
#define UTIL_NEW_FALLBACK_ERROR_LOG(...)                                                           \
    ::Util::FallbackLog::log(__FILE__, __LINE__, __func__, __BASE_FILE__, __VA_ARGS__);

/** A standard catch statement that uses the fallback log to to write an error */
#define UTIL_FALLBACKLOG_CATCH(...)                                                                \
    catch (std::exception & e) {                                                                   \
        UTIL_NEW_FALLBACK_ERROR_LOG(__VA_ARGS__, " because: ", e.what());                          \
    }                                                                                              \
    catch (...) {                                                                                  \
        UTIL_NEW_FALLBACK_ERROR_LOG(                                                               \
            __VA_ARGS__, " because an unknown non-exception was thrown as an exception");          \
    }

namespace Util {

    /** A private struct a user should not create used for the fallback error log
     *  Use UTIL_NEW_FALLBACK_ERROR_LOG to construct this
     */
    class FallbackLog final {
      public:
        /** Log info safely; Note: UTIL_NEW_FALLBACK_ERROR_LOG should be called instead */
        template <typename... Args>
        inline static void log(CCSC fl, const U64 ln, CCSC fn, CCSC bf, Args &&...args) noexcept {
            FallbackLog lg { stderr };
            lg.whoami(fl, ln, fn, bf);
            (lg.put(std::forward<Args>(args)), ...);
        }

      private:
        /** A constructor; Note: UTIL_NEW_FALLBACK_ERROR_LOG should be called instead */
        explicit inline FallbackLog(FILE *const fp_) noexcept : fp { fp_ } {
            put("\n**************************"
                "\n*** Fallback Log Start ***"
                "\n**************************");
        };
        /** Destructor */
        inline ~FallbackLog() noexcept {
            put("\n"
                "\n************************"
                "\n*** Fallback Log End ***"
                "\n************************\n");
            std::fflush(fp);
        }
        SET_IMPLICITS_EXCLUDE_DEFAULT_CTOR(FallbackLog, delete);

        /** Print whoami info */
        inline void whoami(CCSC fl, const U64 ln, CCSC fn, CCSC bf) noexcept {
            std::fprintf(fp, "\nFrom %s: %llu (%s) via %s\n\n", fl, ln, fn, bf);
            std::fflush(fp);
        }

        /** Logs what; specialization for char[]'s */
        template <std::size_t N> inline void put(const char (&what)[N]) noexcept {
            std::fprintf(fp, "%s", what);
        }

        /** Logs what */
        template <typename T> inline void put(T &&what) noexcept {
            using U = Util::Type::RemoveCVR<T>;
            if constexpr (Type::Is::same_ignore_cv<U, const char *>) {
                std::fprintf(fp, "%s", what);
            }
            else if constexpr (Type::Is::same_ignore_cv<U, bool>) {
                std::fprintf(fp, "%s", (what ? "true" : "false"));
            }
            else if constexpr (Type::Is::same_ignore_cv<U, U64>) {
                std::fprintf(fp, "%llu", what);
            }
            else if constexpr (Type::Is::same_ignore_cv<U, std::size_t>) {
                std::fprintf(fp, "%zu", what);
            }
            else {
                static_assert(TD::false_<T>, "Unsupported type passed to fallback log");
            }
        }
        /** The stream to write to */
        FILE *const fp;
    };

} // namespace Util

#endif
