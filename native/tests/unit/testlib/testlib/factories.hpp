/**
 * @file
 * \ingroup testlib
 * @brief This defines a UnitTest error and wrapping macros
 */
#ifndef R_UNIT_TESTLIB_TESTLIB_FACTORIES_HPP_
#define R_UNIT_TESTLIB_TESTLIB_FACTORIES_HPP_

#include "create.hpp"


namespace UnitTest::TestLib::Factories {

    /** Make it easier to create exprs */
    template <typename T = Expr::Bool> Expr::BasePtr t_literal(const Int i = 0) {
        namespace Ex = Expr;
        static_assert(std::is_base_of_v<Ex::Base, T>, "T must derive from Expr::Base");

        if constexpr (std::is_same_v<T, Ex::Bool>) {
            return Create::literal(static_cast<bool>(i));
        }
        else if constexpr (std::is_same_v<T, Ex::String>) {
            return Create::literal(std::to_string(i));
        }
        else if constexpr (std::is_same_v<T, Ex::BV>) {
            return Create::literal(static_cast<UInt>(i));
        }
        else if constexpr (std::is_same_v<T, Ex::FP>) {
            return Create::literal(static_cast<double>(i));
        }
        else if constexpr (std::is_same_v<T, Ex::VS>) {
            return Create::literal(std::make_shared<const PyObj::VS>(i, i, C_CHAR_BIT));
        }
        else {
            static_assert(Util::TD::false_<T>, "Unsupported type T");
        }
    }

} // namespace UnitTest::TestLib::Factories

#endif
