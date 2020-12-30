/**
 * @file
 * @brief Defines the test_each_level function */

#include "utils.hpp"

#include <sstream>


// For brevity
using namespace Utils::Log;
using Lvl = Level::Level;


// Default TEMPLATE_MACRO to empty
#ifndef TEMPLATE_MACRO
    #define TEMPLATE_MACRO
#endif


namespace UnitTest {

    /** Calls <Log function>TEMPLATE_MACRO(args...) for each enabled log level
     *  Then calls test(s, <level>)
     */
    template <typename F, typename... Args>
    void test_each_level(std::ostringstream &s, F &test, const Args &...args) {
        UTILS_LOG_LEVEL_CONSTEXPR const auto lvl = Level::get();

        // Test each level
        if UTILS_LOG_LEVEL_CONSTEXPR
            UTILS_LOG_LEVEL_IMPLIES(lvl, Lvl::Critical) {
                critical TEMPLATE_MACRO(args...);
                test(s, Lvl::Critical);
            }
        if UTILS_LOG_LEVEL_CONSTEXPR
            UTILS_LOG_LEVEL_IMPLIES(lvl, Lvl::Error) {
                error TEMPLATE_MACRO(args...);
                test(s, Lvl::Error);
            }
        if UTILS_LOG_LEVEL_CONSTEXPR
            UTILS_LOG_LEVEL_IMPLIES(lvl, Lvl::Warning) {
                warning TEMPLATE_MACRO(args...);
                test(s, Lvl::Warning);
            }
        if UTILS_LOG_LEVEL_CONSTEXPR
            UTILS_LOG_LEVEL_IMPLIES(lvl, Lvl::Info) {
                info TEMPLATE_MACRO(args...);
                test(s, Lvl::Info);
            }
        if UTILS_LOG_LEVEL_CONSTEXPR
            UTILS_LOG_LEVEL_IMPLIES(lvl, Lvl::Debug) {
                debug TEMPLATE_MACRO(args...);
                test(s, Lvl::Debug);
            }
        if UTILS_LOG_LEVEL_CONSTEXPR
            UTILS_LOG_LEVEL_IMPLIES(lvl, Lvl::Verbose) {
                verbose TEMPLATE_MACRO(args...);
                test(s, Lvl::Verbose);
            }
    }

} // namespace UnitTest
