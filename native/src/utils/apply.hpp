/**
 * @file
 * \ingroup utils
 * @brief This file defines Utils::apply
 */
#ifndef __UTILS_APPLYSTREAM_HPP__
#define __UTILS_APPLYSTREAM_HPP__


namespace Utils {

    /** For each arg, do f(base, arg[i]) starting with i = 0
     *  Func must be a function that accepts two Base & and const T &
     *  This is special definition of apply where only one argument is given.
     */
    template <typename Func, typename Base, typename T>
    constexpr void apply(const Func &f, Base &base, const T &next) {
        (void) f(base, next);
    }

    /** For each arg, do f(base, arg[i]) starting with i = 0
     *  Func must be a function that accepts two Base & and const T &
     */
    template <typename Func, typename Base, typename T, typename... Args>
    constexpr void apply(const Func &f, Base &base, const T &next, const Args &...args) {
        (void) f(base, next);
        apply(f, base, args...);
    }

    /** For each arg, do f(base, arg[i]) starting with i = 0
     *  Func must be a class with the static method f defined
     *  This is special definition of apply where only one argument is given.
     */
    template <typename Func, typename Base, typename T>
    constexpr void apply(Base &base, const T &next) {
        (void) Func::f(base, next);
    }

    /** For each arg, do f(base, arg[i]) starting with i = 0
     *  Func must be a class with the static method f defined
     */
    template <typename Func, typename Base, typename T, typename... Args>
    constexpr void apply(Base &base, const T &next, const Args &...args) {
        (void) Func::f(base, next);
        apply<Func>(base, args...);
    }

} // namespace Utils

#endif
