/**
 * @file
 * \ingroup testlib
 * @brief This defines a UnitTest error and wrapping macros
 */
#ifndef R_TESTS_UNIT_TESTLIB_TESTLIB_FACTORIES_HPP_
#define R_TESTS_UNIT_TESTLIB_TESTLIB_FACTORIES_HPP_

#include "create.hpp"


namespace UnitTest::TestLib::Factories {

    /** Make it easier to create exprs */
    template <typename T = Expr::Bool> Expr::BasePtr t_literal(const I64 i = 0) {
        static_assert(std::is_base_of_v<Expr::Base, T>, "T must derive from Expr::Base");
        if constexpr (std::is_same_v<T, Expr::Bool>) {
            return Create::literal(static_cast<bool>(i));
        }
        else if constexpr (std::is_same_v<T, Expr::String>) {
            return Create::literal(std::to_string(i));
        }
        else if constexpr (std::is_same_v<T, Expr::BV>) {
            return Create::literal(static_cast<U64>(i));
        }
        else if constexpr (std::is_same_v<T, Expr::FP>) {
            return Create::literal(static_cast<double>(i));
        }
        else if constexpr (std::is_same_v<T, Expr::VS>) {
            return Create::literal(std::make_shared<const PyObj::VS>(i, i, CHAR_BIT));
        }
        else {
            static_assert(Util::TD::false_<T>, "Unsupported type T");
        }
    }

} // namespace UnitTest::TestLib::Factories

#endif
