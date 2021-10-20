/**
 * @file
 * \ingroup utils
 * @brief This file defines the ostream logging backend
 */
#ifndef R_UTILS_LOG_BACKEND_OSTREAM_HPP_
#define R_UTILS_LOG_BACKEND_OSTREAM_HPP_

#include "base.hpp"

#include "../../affirm.hpp"
#include "../../error.hpp"

#include <exception>
#include <memory>
#include <mutex>
#include <ostream>


namespace Utils::Log::Backend {

    /** The stream backend
     *  This takes in an ostream and logs to it
     *  Note, we do logging in a threadsafe context
     */
    struct OStream : public Base {

        /** Constructor: Use default with initializer list
         *  If flush, every time s is written to the contents are flushed; by default flush = true
         *  Note: if the ostream is constructed by sharing a buffer with a static like std::cout
         *  or something, flush_on_exit should be false as static destruction is done without
         *  a defined order.
         */
        explicit inline OStream(std::shared_ptr<std::ostream> stream_, const bool flush_,
                                const bool flush_on_exit_ = true) noexcept
            : stream(std::move(stream_)), flush(flush_), flush_on_exit(flush_on_exit_) {
            Utils::affirm<Utils::Error::Unexpected::Usage>(stream != nullptr, WHOAMI_WITH_SOURCE,
                                                           "stream may not be a null shared_ptr");
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

        /** Log the message */
        inline void log(CCSC, const Level::Level &, const std::string &msg) const override final {
            std::lock_guard<decltype(m)> lock(m);
            *stream << msg << "\n";
            if (flush) {
                stream->flush();
            }
        }

      private:
        /** The stream we log to; this may not be nullptr */
        const std::shared_ptr<std::ostream> stream;

        /** If true, every time stream is written to the contents are flushed */
        const bool flush;

        /** True if the stream should be flushed at exit */
        const bool flush_on_exit;

        /** A mutex to ensure logging is threadsafe */
        mutable std::mutex m;
    };

} // namespace Utils::Log::Backend

#endif
