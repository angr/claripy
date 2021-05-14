/**
 * @file
 * \ingroup utils
 * @brief This file defines way to transfer the constness of one type onto another
 */
#ifndef R_UTILS_TRANSFERCONST_HPP_
#define R_UTILS_TRANSFERCONST_HPP_

#include <type_traits>


namespace Utils {

    /** Returns a const Out if In is const, else Out */
    template <typename Out, typename In>
    using TransferConst = std::conditional_t<std::is_const_v<In>, const Out, Out>;

} // namespace Utils

#endif
