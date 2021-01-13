/**
 * @file
 * \ingroup testlib
 * @brief This defines a UnitTest error and wrapping macros
 */
#ifndef __TESTS_UNIT_TESTLIB_TESTLIB_FACTORY_HPP__
#define __TESTS_UNIT_TESTLIB_TESTLIB_FACTORY_HPP__

#include "expression.hpp"
#include "utils.hpp"


namespace UnitTest::TestLib {

    /** Make it easier to create expressions */
    template <typename T, typename... Args> T literal_factory(Args... args) {
        std::vector<std::shared_ptr<Annotation::Base>> a;
        return Expression::factory<T>(a, args...);
    }

    /** Make a concrete literal int */
    Expression::ConcreteIntLiteral literal_int(const Constants::Int i = 0);

} // namespace UnitTest::TestLib

#endif
