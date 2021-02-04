/**
 * @file
 * \ingroup utils
 * @brief This file defines way to transfer the constness of one type onto another
 */
#ifndef __UTILS_TRANSFERCONST_HPP__
#define __UTILS_TRANSFERCONST_HPP__

#include <type_traits>


namespace Utils {

	/** Returns a const Out if In is const, else Out */
	template <typename Out, typename In>
	using TransferConst = std::conditional_t<std::is_const_v<In>, const Out, Out>;

}

#endif
