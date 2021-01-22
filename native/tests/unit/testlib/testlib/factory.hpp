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
    template <typename T> T literal_factory(const Constants::Int i) {
        std::vector<std::shared_ptr<Annotation::Base>> a;
        Constants::CCSC cs = (Constants::CCSC) &i;
        const std::string s(cs, 8);
        return Expression::factory<T>(a, 64_i, s);
    }

    /** Make a concrete literal int */
    Expression::ConcreteIntLiteral literal_int(const Constants::Int i = 0);

} // namespace UnitTest::TestLib

#endif
