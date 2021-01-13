/**
 * @file
 * \ingroup unittest
 * @brief Defines the test_each_level function
 */
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
     *  Then calls test(test_arg, <level>)
     */
    template <typename F, typename TestArg, typename... Args>
    void test_each_level(TestArg &test_arg, F &test, const Args &...args) {
        if UTILS_LOG_LEVEL_CONSTEXPR (Level::enabled(Lvl::Critical)) {
            critical TEMPLATE_MACRO(args...);
            test(test_arg, Lvl::Critical);
        }
        if UTILS_LOG_LEVEL_CONSTEXPR (Level::enabled(Lvl::Error)) {
            error TEMPLATE_MACRO(args...);
            test(test_arg, Lvl::Error);
        }
        if UTILS_LOG_LEVEL_CONSTEXPR (Level::enabled(Lvl::Warning)) {
            warning TEMPLATE_MACRO(args...);
            test(test_arg, Lvl::Warning);
        }
        if UTILS_LOG_LEVEL_CONSTEXPR (Level::enabled(Lvl::Info)) {
            info TEMPLATE_MACRO(args...);
            test(test_arg, Lvl::Info);
        }
        if UTILS_LOG_LEVEL_CONSTEXPR (Level::enabled(Lvl::Debug)) {
            debug TEMPLATE_MACRO(args...);
            test(test_arg, Lvl::Debug);
        }
        if UTILS_LOG_LEVEL_CONSTEXPR (Level::enabled(Lvl::Verbose)) {
            verbose TEMPLATE_MACRO(args...);
            test(test_arg, Lvl::Verbose);
        }
    }

} // namespace UnitTest
