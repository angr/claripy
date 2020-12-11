#ifndef __SET_JOIN_HPP__
#define __SET_JOIN_HPP__

#include <set>


// TODO: cleanup

namespace Utils {

namespace Private {
template <typename T>
void set_join_helper(std::set<T> & ret, const std::set<T> & a) {
	ret.insert(a.begin(), a.end());
}

template <typename T, typename... Args>
void set_join_helper(std::set<T> & ret, const std::set<T> & a, const Args... args) {
	ret.insert(a.begin(), a.end());
	set_join_helper(ret, args...);
}
}

template <typename T, typename... Args>
std::set<T> set_join(const Args... args) {
	auto ret = std::set<T>();
	Private::set_join_helper<T>(ret, args...);
	return ret;
}

}
#endif
