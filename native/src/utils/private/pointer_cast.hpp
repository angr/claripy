/**
 * @file
 * \ingroup utils
 * @brief This file defines private pointer cast methods
 * These methods preserve the constness of the internal type
 */
#ifndef __UTILS_PRIVATE_POINTERCAST_HPP__
#define __UTILS_PRIVATE_POINTERCAST_HPP__

#include <memory>
#include <type_traits>


namespace Utils::Private {

	/** The return type of a cast
	 *  Returns const Out if In is const, else Out
	 */
	template <typename Out, typename In>
	using TrueOut = std::conditional_t<std::is_const_v<In>, const Out, Out>;

	/** A const preserving static pointer cast */
	template <typename Out, typename In, typename RealOut =
	constexpr inline auto static_pointer_cast(const TrueIn &in) noexcept {
		return std::static_pointer_cast<TrueOut<Out, In>>(in);
	}

	/** An unchecked dynamic pointer cast */
	template <typename Out, typename In, typename RealOut = TrueOut<Out, In>>
	constexpr inline auto dynamic_pointer_cast(const TrueIn &in) noexcept {
		return std::dynamic_pointer_cast<TrueOut<Out, In>>(in);
	}

}

#endif
