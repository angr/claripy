/**
 * @file
 * \ingroup utils
 * @brief This file defines a function run_function(f, args) that returns f(args)
 * Note that args are passed by const reference
 */
#ifndef __UTILS_RUNCRFUNCTION_HPP__
#define __UTILS_RUNCRFUNCTION_HPP__


namespace Utils {

    /** Return f(args...) */
    template <typename F, typename... Args>
    inline auto run_cr_function(const F &f, const Args &...args) {
        return f(args...);
    };

} // namespace Utils

#endif
