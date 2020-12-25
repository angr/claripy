/**
 * @file
 * @brief This file defines the AbstractBase Log Style class
 */
#ifndef __UTILS_LOG_STYLE_ABSTRACTBASE_HPP__
#define __UTILS_LOG_STYLE_ABSTRACTBASE_HPP__

#include "../level.hpp"


namespace Utils::Log::Style {

    /** The base Log Style class
     *  All log styles must subclass this
     *  The subclass must implement the () operator defined below
     */
    struct AbstractBase {
        /** Format the log message
         *  Ownership of raw is transferred
         */
        virtual std::string operator()(const Level &lvl, std::ostringstream &raw) const;

      protected:
        /** Force this class to be purely abstract
         *  We do not declare the operator()=0 because we want to use this class
         *  as if it were instantiatable
         */
        AbstractBase();
    };

} // namespace Utils::Log::Style

#endif
