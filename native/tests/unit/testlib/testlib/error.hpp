/**
 * @file
 * \ingroup testlib
 * @brief This defines a UnitTest error and wrapping macros
 */
#ifndef R_UNIT_TESTLIB_TESTLIB_ERROR_HPP_
#define R_UNIT_TESTLIB_TESTLIB_ERROR_HPP_

#include "util.hpp"


/** A unittest macro used to throw an error */
#define UNITTEST_ERR(...) throw UnitTest::TestLib::Error(__VA_ARGS__);

/** A unittest assertion macro */
#define UNITTEST_ASSERT(B)                                                                        \
    if (!(B)) {                                                                                   \
        UnitTest::TestLib::ut_fail(WHOAMI_WITH_SOURCE, "UnitTest Assertion failed.");             \
    }

/** A unittest assertion macro */
#define UNITTEST_ASSERT_MSG(B, ...)                                                               \
    if (!(B)) {                                                                                   \
        UnitTest::TestLib::ut_fail(WHOAMI_WITH_SOURCE, "UnitTest Assertion failed.",              \
                                   __VA_ARGS__);                                                  \
    }


namespace UnitTest::TestLib {

    /** The original log backend */
    extern thread_local std::shared_ptr<const Util::Log::Backend::Base> original_bk;

    /** The original log style */
    extern thread_local std::shared_ptr<const Util::Log::Style::Base> original_sty;

    /** The UnitTest error struct */
    DEFINE_NAMESPACED_FINAL_EXCEPTION(Error, Claricpp, Util::Err)

    /** A function used to test a boolean value */
    template <typename... Args> void ut_fail(Args &&...args) {
        if (original_bk != nullptr) {
            auto copy { original_bk }; // Just in case someone is dumb and catches the error
            Util::Log::Backend::unsafe_set(std::move(original_bk));
        }
        if (original_sty != nullptr) {
            auto copy { original_sty }; // Just in case someone is dumb and catches the error
            Util::Log::Style::unsafe_set(std::move(original_sty));
        }
        // Do not catch this
        UNITTEST_ERR(std::forward<Args>(args)...);
    }

} // namespace UnitTest::TestLib

#endif
