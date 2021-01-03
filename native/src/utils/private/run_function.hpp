/**
 * @file
 * \ingroup utils
 * @brief This file defines a function run_function(f, args) that returns f(args)
 */
#ifndef __UTILS_PRIVATE_RUNFUNCTION_HPP__
#define __UTILS_PRIVATE_RUNFUNCTION_HPP__


namespace Utils::Private {

    /** Return f(args...) */
    template <typename F, typename... Args>
    inline auto run_function(const F &f, const Args &...args) {
        return f(args...);
    };

    /** Return f() */
    template <typename F> inline auto run_function(const F &f) { return f(); };

} // namespace Utils::Private

#endif
