/**
 * @file
 * \ingroup testlib
 * @brief This defines a UnitTest error and wrapping macros
 */
#ifndef __TESTS_UNIT_TESTLIB_TESTLIB_FACTORIES_HPP__
#define __TESTS_UNIT_TESTLIB_TESTLIB_FACTORIES_HPP__

#include "annotation.hpp"
#include "expression.hpp"
#include "factory.hpp"
#include "utils.hpp"


namespace UnitTest::TestLib::Factories {

    /** Create a simple Symbol */
    inline auto symbol(std::string name = std::string { "hi" }) { Op::factory<Op::Symbol>(name); }

    /** Create a simple Literal */
    inline Factory::Ptr<Op::Literal> literal(const Constants::Int i = 0) {
        const constexpr Constants::UInt size { sizeof(Constants::Int) };
        char buf[size];                                                // NOLINT
        std::memcpy(buf, reinterpret_cast<Constants::CCSC>(&i), size); // NOLINT
        Constants::CCSC cs { buf };
        return Op::factory<Op::Literal>(cs, Constants::UInt { sizeof(i) });
    }

    /** Make it easier to create expressions */
    template <typename T = Expression::Int> Factory::Ptr<T> t_literal(const Constants::Int i = 0) {
        static_assert(std::is_base_of_v<Expression::Base, T>,
                      "T must derive from Expression::Base");
        auto ans { std::vector<Factory::Ptr<Annotation::Base>> {} };
        auto op { literal(i) };
        auto baseop { Utils::up_cast<Op::Base>(op) };
        if constexpr (std::is_base_of_v<Expression::Bits, T>) {
            return Expression::factory<T>(false, std::move(baseop), std::move(ans),
                                          Constants::UInt { sizeof(i) });
        }
        else {
            return Expression::factory<T>(false, std::move(baseop), std::move(ans));
        }
    }

} // namespace UnitTest::TestLib::Factories

#endif
