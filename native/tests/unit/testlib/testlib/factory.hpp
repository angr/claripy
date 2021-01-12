/**
 * @file
 * @brief This defines a UnitTest error and wrapping macros
 */
#ifndef __TESTS_UNIT_TESTLIB_TESTLIB_FACTORY_HPP__
#define __TESTS_UNIT_TESTLIB_TESTLIB_FACTORY_HPP__

#include "expression.hpp"
#include "utils.hpp"


namespace UnitTest::TestLib {

    Expression::ConcreteIntLiteral literal_factory(Constants::Int i);

} // namespace UnitTest::TestLib

#endif
