/**
 * @file
 * \ingroup testlib
 * @brief This defines a UnitTest error and wrapping macros
 */
#ifndef R_UNIT_TESTLIB_TESTLIB_ERROR_HPP_
#define R_UNIT_TESTLIB_TESTLIB_ERROR_HPP_

#include "util.hpp"


/** A unittest macro used to throw an error */
#define UNITTEST_ERR(...) UTIL_THROW(UnitTest::TestLib::Error, __VA_ARGS__);

/** A unittest assertion macro */
#define UNITTEST_ASSERT(B)                                                                         \
    if (!(B)) {                                                                                    \
        UnitTest::TestLib::ut_fail("UnitTest Assertion failed.");                                  \
    }

/** A unittest assertion macro */
#define UNITTEST_ASSERT_MSG(B, ...)                                                                \
    if (!(B)) {                                                                                    \
        UnitTest::TestLib::ut_fail(Util::to_str("UnitTest Assertion failed.", __VA_ARGS__));       \
    }


namespace UnitTest::TestLib {

    /** The original log backend */
    extern thread_local std::shared_ptr<const Util::Log::Backend::Base> original_bk;

    /** The original log style */
    extern thread_local std::shared_ptr<const Util::Log::Style::Base> original_sty;

    /** The UnitTest error struct */
    UTIL_ERR_DEFINE_NAMESPACED_FINAL_EXCEPTION(Error, Claricpp, Util::Err)

    /** A function used to fail a unit test; the thrown exception should *not* be caught */
    template <typename... Args> void ut_fail(std::string &&msg) {
        if (original_bk != nullptr) {
            auto copy { original_bk }; // Just in case someone is dumb and catches the error
            Util::Log::Backend::unsafe_set(std::move(original_bk));
        }
        if (original_sty != nullptr) {
            auto copy { original_sty }; // Just in case someone is dumb and catches the error
            Util::Log::Style::unsafe_set(std::move(original_sty));
        }
        // Do not catch this
        UNITTEST_ERR(std::move(msg));
    }

} // namespace UnitTest::TestLib

#endif
