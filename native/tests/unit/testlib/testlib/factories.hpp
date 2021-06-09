/**
 * @file
 * \ingroup testlib
 * @brief This defines a UnitTest error and wrapping macros
 */
#ifndef R_UNIT_TESTLIB_TESTLIB_FACTORIES_HPP_
#define R_UNIT_TESTLIB_TESTLIB_FACTORIES_HPP_

#include "create.hpp"

#include <string>


namespace UnitTest::TestLib::Factories {

    /** Make it easier to create expressions */
    template <typename T = Expression::Bool>
    Expression::BasePtr t_literal(const Constants::Int i = 0) {
        namespace Ex = Expression;
        static_assert(std::is_base_of_v<Ex::Base, T>, "T must derive from Expression::Base");

        if constexpr (std::is_same_v<T, Ex::Bool>) {
            return Create::literal(static_cast<bool>(i));
        }
        else if constexpr (std::is_same_v<T, Ex::String>) {
            return Create::literal(std::to_string(i));
        }
        else if constexpr (std::is_same_v<T, Ex::BV>) {
            std::vector<std::byte> data;
            data.resize(sizeof(Constants::Int));
            UTILS_TYPE_PUN_ONTO(std::byte, data.data(), &i, true);
            return Create::literal(std::move(data));
        }
        else if constexpr (std::is_same_v<T, Ex::FP>) {
            return Create::literal(static_cast<double>(i));
        }
        else if constexpr (std::is_same_v<T, Ex::VS>) {
            return Create::literal(std::make_shared<const PyObj::VS>(i, i, C_CHAR_BIT));
        }
        else {
            static_assert(Utils::TD::false_<T>, "Unsupported type T");
        }
    }

} // namespace UnitTest::TestLib::Factories

#endif
