/**
 * @file
 * \ingroup util
 * @brief This file defines way to transfer the const-ness of one type onto another
 */
#ifndef R_SRC_UTIL_TYPE_TRANSFERCONST_HPP_
#define R_SRC_UTIL_TYPE_TRANSFERCONST_HPP_

#include <type_traits>


namespace Util::Type {

    /** Returns a const Out if In is const, else Out */
    template <typename Out, typename In>
    using TransferConst = std::conditional_t<std::is_const_v<In>, const Out, Out>;

} // namespace Util::Type

#endif
