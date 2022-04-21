/**
 * @file
 * \ingroup unittest
 * @brief Defines the test_each_level function
 */
#ifndef R_TESTS_UNIT_UTIL_LOG_TESTEACHLEVEL_HPP_
#define R_TESTS_UNIT_UTIL_LOG_TESTEACHLEVEL_HPP_

#include <src/util.hpp>
#include <sstream>


// For brevity
using namespace Util::Log;


// Default TEMPLATE_MACRO to empty
#ifndef TEMPLATE_MACRO
    /** The template arguments to pass to the log functions, including the <>'s
     *  Note: We use a macro here instead of a real template to allow testing of
     *  the non-templated version of the log functions
     */
    #define TEMPLATE_MACRO
#endif


namespace UnitTest {

    /** Calls <Log function>TEMPLATE_MACRO(args...) for each enabled log level
     *  Then calls test(test_arg, <level>)
     */
    template <typename F, typename TestArg, typename... Args>
    void test_each_level(TestArg &test_arg, F &test, const Args &...args) {
        if UTIL_LOG_LEVEL_CONSTEXPR (Level::enabled(Level::critical)) {
            critical TEMPLATE_MACRO(args...);
            test(test_arg, Level::critical);
        }
        if UTIL_LOG_LEVEL_CONSTEXPR (Level::enabled(Level::error)) {
            error TEMPLATE_MACRO(args...);
            test(test_arg, Level::error);
        }
        if UTIL_LOG_LEVEL_CONSTEXPR (Level::enabled(Level::warning)) {
            warning TEMPLATE_MACRO(args...);
            test(test_arg, Level::warning);
        }
        if UTIL_LOG_LEVEL_CONSTEXPR (Level::enabled(Level::info)) {
            info TEMPLATE_MACRO(args...);
            test(test_arg, Level::info);
        }
        if UTIL_LOG_LEVEL_CONSTEXPR (Level::enabled(Level::debug)) {
            debug TEMPLATE_MACRO(args...);
            test(test_arg, Level::debug);
        }
        if UTIL_LOG_LEVEL_CONSTEXPR (Level::enabled(Level::verbose)) {
            verbose TEMPLATE_MACRO(args...);
            test(test_arg, Level::verbose);
        }
    }

} // namespace UnitTest


#endif
