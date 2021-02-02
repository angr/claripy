/**
 * @file
 * \ingroup utils
 * @brief This file defines the ostream logging backend
 */
#ifndef __UTILS_LOG_BACKEND_OSTREAM_HPP__
#define __UTILS_LOG_BACKEND_OSTREAM_HPP__

#include "base.hpp"

#include <memory>
#include <mutex>
#include <ostream>


namespace Utils::Log::Backend {

    /** The stream backend
     *  This takes in an ostream and logs to it
     *  Note, we do logging in a threadsafe context
     */
    struct OStream : public Base {

        /** Constructor: Use default with initalizer list
         *  If flush, every time s is written to the contents are flushed; by default flush = true
         *  Note: if the ostream is constructed by sharing a buffer with a static like std::cout
         *  or something, flush_on_exit should be false as static destruction is done without
         *  a defined order.
         */
        explicit inline OStream(std::shared_ptr<std::ostream> stream_, const bool flush_,
                                const bool flush_on_exit_ = true) noexcept
            : stream(std::move(stream_)), flush(flush_), flush_on_exit(flush_on_exit_) {}

        /** A virtual destructor */
        virtual inline ~OStream() {
            if (this->flush_on_exit) {
                this->stream->flush();
            }
        }

        // We don't want to mess with the shared ostream
        SET_IMPLICITS_EXCLUDE_DEFAULT_CTOR(OStream, delete)

        /** Log the message */
        inline void log(Constants::CCSC, const Level::Level &,
                        const std::string &msg) override final {
            std::lock_guard<decltype(this->m)> lock(m);
            *stream << msg << "\n";
            if (this->flush) {
                this->stream->flush();
            }
        }

      private:
        /** The stream we log to */
        std::shared_ptr<std::ostream> stream;

        /** If true, every time stream is written to the contents are flushed */
        const bool flush;

        /** True if the stream should be flushed at exit */
        const bool flush_on_exit;

        /** A mutex to ensure logging is threadsafe */
        mutable std::mutex m;
    };

} // namespace Utils::Log::Backend

#endif
