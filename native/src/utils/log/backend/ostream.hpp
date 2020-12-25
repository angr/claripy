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

        /** Log the message */
        void operator()(Constants::CCSC id, const Level &lvl,
                        const std::string &msg) const override final;

      protected:
        /** Require subclass to construct */
        OStream(const std::ostream &s);

      private:
        /** The stream we write to */
        const std::ostream stream;

        /** Delete default constructor */
        OStream() = delete;
    };

} // namespace Utils::Log::Backend

#endif
