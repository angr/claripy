/**
 * @file
 * @brief This file defines the default log style class
 */
#ifndef __UTILS_LOG_STYLE_ABSTRACTBASE_HPP__
#define __UTILS_LOG_STYLE_ABSTRACTBASE_HPP__

#include "../level.hpp"

#include <sstream>


/** A namespace used for the utils directory */
namespace Utils::Log::Style {

    /** The base log style class
     *  All log styles must subclass this
     *  Log functions must implement
     */
    struct AbstractBase {
        /** Format the log message
         *  Ownership of raw is transferred
         */
        virtual std::string operator()(const Level &lvl, std::ostringstream &raw) const;

      protected:
        /** Force this class to be purely abstract
         *  We do not declare the operator()=0 because we want to use this class
         * as if it were instantiatable
         */
        AbstractBase();
    };

} // namespace Utils::Log::Style

#endif
