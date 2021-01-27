/**
 * @file
 * \ingroup utils
 * @brief This file defines the ostream logging backend
 */
#ifndef __UTILS_LOG_BACKEND_OSTREAM_HPP__
#define __UTILS_LOG_BACKEND_OSTREAM_HPP__

#include "abstract_base.hpp"

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
        explicit OStream(std::shared_ptr<std::ostream> s, const bool flush,
                         const bool flush_on_exit = true);

        /** A virtual destructor */
        virtual ~OStream();

        // We don't want to mess with the shared ostream
        SET_IMPLICITS_EXCLUDE_DEFAULT_CONSTRUCTOR(OStream, delete)

        /** Log the message */
        void log(Constants::CCSC id, const Level::Level &lvl,
                 const std::string &msg) override final;

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
