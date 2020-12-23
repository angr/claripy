/**
 * @file
 * @brief This file defines Utils::apply_stream
 */
#ifndef __UTILS_APPLYSTREAM_HPP__
#define __UTILS_APPLYSTREAM_HPP__


/** A namespace used for the utils directory */
namespace Utils {

    /** For each arg, do f(base, arg[i]) starting with i = 0
     *  Func must be a class with the static method f defined
     *  This is special definition of apply where only one argument is given.
     */
    template <typename Func, typename Base, typename T> void apply(Base &base, const T &next) {
        (void) Func::f(base, next);
    }

    /** For each arg, do f(base, arg[i]) starting with i = 0
     *  Func must be a class with the static method f defined
     */
    template <typename Func, typename Base, typename T, typename... Args>
    void apply(Base &base, const T &next, const Args &...args) {
        (void) Func::f(base, next);
        apply<Func>(base, args...);
    }

} // namespace Utils

#endif
