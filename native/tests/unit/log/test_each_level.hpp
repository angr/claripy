/**
 * @file
 * @brief Defines the test_each_level function */

#include "utils.hpp"

#include <sstream>

using namespace Utils::Log;
using Lvl = Level::Level;


namespace UnitTest {

    /** Calls the log function on (args...) for each enabled log level
     *  Then calls test(s)
     */
    template <typename F, typename... Args>
    void test_each_level(std::ostringstream &s, F &test, const Args &...args) {
        const UTILS_LOG_LEVEL_CONSTANT auto lvl = Level::get();

        // Test each level
        if UTILS_LOG_LEVEL_CONSTANT
            UTILS_LOG_LEVEL_IMPLIES(lvl, Lvl::Critical) {
                critical(args...);
                test(s);
            }
        if UTILS_LOG_LEVEL_CONSTANT
            UTILS_LOG_LEVEL_IMPLIES(lvl, Lvl::Error) {
                error(args...);
                test(s);
            }
        if UTILS_LOG_LEVEL_CONSTANT
            UTILS_LOG_LEVEL_IMPLIES(lvl, Lvl::Warning) {
                warning(args...);
                test(s);
            }
        if UTILS_LOG_LEVEL_CONSTANT
            UTILS_LOG_LEVEL_IMPLIES(lvl, Lvl::Info) {
                info(args...);
                test(s);
            }
        if UTILS_LOG_LEVEL_CONSTANT
            UTILS_LOG_LEVEL_IMPLIES(lvl, Lvl::Debug) {
                debug(args...);
                test(s);
            }
        if UTILS_LOG_LEVEL_CONSTANT
            UTILS_LOG_LEVEL_IMPLIES(lvl, Lvl::Verbose) {
                verbose(args...);
                test(s);
            }
    }

} // namespace UnitTest
