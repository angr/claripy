/**
 * @file
 * \ingroup util
 * @brief This file defines a bool that determines if T has the pre ++ operator defined
 */
#ifndef R_SRC_UTIL_TYPE_HAS_PREINCOP_HPP_
#define R_SRC_UTIL_TYPE_HAS_PREINCOP_HPP_

#include "../sfinae_test.hpp"

#include <utility>


namespace Util::Type::Has {

    /** A struct which determines if T has an ++T op defined
     *  template <typename T> constexpr bool pre_inc_op = is_this_valid(++std::declval<T>());
     */
    UTIL_TYPE_SFINAETEST(pre_inc_op, ++std::declval<T>(), typename T)

} // namespace Util::Type::Has

#endif
