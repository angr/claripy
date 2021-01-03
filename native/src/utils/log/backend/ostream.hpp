/**
 * @file
 * \ingroup utils
 * @brief This file defines the ostream logging backend
 */
#ifndef __UTILS_LOG_BACKEND_OSTREAM_HPP__
#define __UTILS_LOG_BACKEND_OSTREAM_HPP__

#include "abstract_base.hpp"

#include "../../../unittest.hpp"

#include <mutex>
#include <ostream>


namespace Utils::Log::Backend {

    /** The stream backend
     *  This takes in an ostream and logs to it
     *  Note, we do logging in a threadsafe context
     */
    struct OStream : public AbstractBase {

        /** Constructor: Keeps a reference to the passed stream; do not destroy s!
         *  If flush, every time s is written to the contents are flushed; by default flush = true
         *  Warning: the passes ostream may not be closed or destroyed !
         *  Note: Because copying an ostream doesn't really make sense we use references
         */
        OStream(std::ostream &s, const bool flush = true);

        /** Default pure virtual destructor */
        ~OStream() = default;

        /** Log the message */
        void log(Constants::CCSC id, const Level::Level &lvl,
                 const std::string &msg) override final;

      private:
        /** The stream we write to
         *  Declared as mutable to allow writing to the stream from const methods
         */
        std::ostream &stream;

        /** If true, every time stream is written to the contents are flushed */
        const bool flush;

        /** A mutex to ensure logging is threadsafe */
        mutable std::mutex m;

        /** Delete default constructor */
        OStream() = delete;

        /** Allow unittesting */
        ENABLE_UNITTEST_FRIEND_ACCESS
    };

} // namespace Utils::Log::Backend

#endif
