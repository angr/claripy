/**
 * @file
 * \ingroup testlib
 * @brief This defines a UnitTest error and wrapping macros
 */
#ifndef R_TESTS_UNIT_TESTLIB_TESTLIB_ERROR_HPP_
#define R_TESTS_UNIT_TESTLIB_TESTLIB_ERROR_HPP_

#include <src/util.hpp>


/** A unittest macro used to throw an error */
#define UNITTEST_ERR(...) UTIL_THROW(UnitTest::TestLib::Error, __VA_ARGS__);

/** A unittest assertion macro */
#define UNITTEST_ASSERT(B)                                                                         \
    if (!(B)) {                                                                                    \
        UnitTest::TestLib::ut_fail(Util::to_str(WHOAMI "UnitTest Assertion failed."));             \
    }

/** A unittest assertion macro */
#define UNITTEST_ASSERT_MSG(B, ...)                                                                \
    if (!(B)) {                                                                                    \
        UnitTest::TestLib::ut_fail(                                                                \
            Util::to_str(WHOAMI "UnitTest Assertion failed.", __VA_ARGS__));                       \
    }


namespace UnitTest::TestLib {

    /** The UnitTest error struct */
    UTIL_ERR_DEFINE_NAMESPACED_FINAL_EXCEPTION(Error, Claricpp, Util::Err)

#ifndef CONSTANT_LOG_LEVEL
    /** The original log backend */
    extern thread_local std::shared_ptr<const Util::Log::Backend::Base> original_bk;

    /** The original log style */
    extern thread_local std::shared_ptr<const Util::Log::Style::Base> original_sty;

    /** A function used to fail a unit test; the thrown exception should *not* be caught */
    [[noreturn]] inline void ut_fail(std::string &&msg) {
        if (original_bk != nullptr && original_bk != Util::Log::Backend::get()) {
            auto copy { original_bk }; // Just in case someone is dumb and catches the error
            Util::Log::Backend::silent_less_safe_set(std::move(original_bk));
        }
        if (original_sty != nullptr && original_sty != Util::Log::Style::get()) {
            auto copy { original_sty }; // Just in case someone is dumb and catches the error
            Util::Log::Style::silent_less_safe_set(std::move(original_sty));
        }
        // Do not catch this
        throw UnitTest::TestLib::Error { std::move(msg) };
    }
#else
    /** A function used to fail a unit test; the thrown exception should *not* be caught */
    [[noreturn]] inline void ut_fail(std::string &&msg) {
        // Do not catch this
        throw UnitTest::TestLib::Error { std::move(msg) };
    }
#endif

} // namespace UnitTest::TestLib

#endif
