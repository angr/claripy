/**
 * @file
 * @brief This file defines the ostream logging backend
 */
#ifndef __UTILS_LOG_BACKEND_OSTREAM_HPP__
#define __UTILS_LOG_BACKEND_OSTREAM_HPP__

#include "abstract_base.hpp"

#include <ostream>


namespace Utils::Log::Backend {

    /** The stream backend
     *  This takes in an ostream and logs to it
     */
    struct OStream : public AbstractBase {

        /** Constructor: Keeps a reference to the passed stream; do not destroy s!
         *  Warning: the passes ostream may not be closed or destroyed !
         *  Note: Because copying an ostream doesn't really make sense we use references
         */
        OStream(std::ostream &s);

        /** Default pure virtual destructor */
        ~OStream() = default;

        /** Log the message */
        void log(Constants::CCSC id, const Level &lvl, const std::string &msg) override final;

      private:
        /** The stream we write to
         *  Declared as mutable to allow writing to the stream from const methods
         */
        std::ostream &stream;

        /** Delete default constructor */
        OStream() = delete;
    };

} // namespace Utils::Log::Backend

#endif
