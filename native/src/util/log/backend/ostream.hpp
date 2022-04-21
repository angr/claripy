/**
 * @file
 * \ingroup util
 * @brief This file defines the ostream logging backend
 */
#ifndef R_SRC_UTIL_LOG_BACKEND_OSTREAM_HPP_
#define R_SRC_UTIL_LOG_BACKEND_OSTREAM_HPP_

#include "multiplex.hpp"

#include "../style.hpp"

#include <mutex>
#include <ostream>


namespace Util::Log::Backend {

    /** The stream backend
     *  This takes in an ostream and logs to it
     *  Note, we do logging in a threadsafe context
     */
    struct OStream : public Multiplexable {
        /** Backend name */
        inline const char *name() const noexcept override { return "OStream"; }

        /** Constructor: Use default with initializer list
         *  If flush, every time s is written to the contents are flushed; by default flush = true
         *  Note: if the ostream is constructed by sharing a buffer with a static like std::cout
         *  or something, flush_on_exit should be false as static destruction is done without
         *  a defined order.
         */
        explicit inline OStream(std::shared_ptr<std::ostream> stream_, const bool should_flush_,
                                const bool flush_on_exit_ = true)
            : stream { std::move(stream_) },
              should_flush { should_flush_ },
              flush_on_exit { flush_on_exit_ } {
            UTIL_ASSERT(Err::Null, stream, "stream should not be nullptr");
        }

        /** A virtual destructor */
        inline ~OStream() noexcept override {
            if (flush_on_exit) {
                try {
                    stream->flush();
                }
                // We are in a destructor, do not propagate exceptions
                catch (std::exception &) {
                }
            }
        }

        // We don't want to mess with the shared ostream
        SET_IMPLICITS_EXCLUDE_DEFAULT_CTOR(OStream, delete)

        /** Log the given message */
        inline void log(CCSC id, const Level::Lvl lvl, Util::LazyStr &&msg) const final {
            log_str(id, lvl, msg());
        }

        /** Log the given string message */
        inline void log_str(CCSC id, const Level::Lvl lvl, std::string &&msg) const final {
            std::string out { Style::get()->str(id, lvl, std::move(msg)) };
            std::lock_guard<decltype(m)> lock(m);
            *stream << std::move(out) << '\n';
            if (should_flush) {
                flush();
            }
        }

        /** Flush the log */
        inline void flush() const final { stream->flush(); }

      private:
        /** The stream we log to; this may not be nullptr */
        const std::shared_ptr<std::ostream> stream;

        /** If true, every time stream is written to the contents are flushed */
        const bool should_flush;

        /** True if the stream should be flushed at exit */
        const bool flush_on_exit;

        /** A mutex to ensure logging is threadsafe */
        mutable std::mutex m;
    };

} // namespace Util::Log::Backend

#endif
