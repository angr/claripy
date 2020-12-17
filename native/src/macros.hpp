/**
 * @file
 * @brief This file contains macros used across claricpp
 */
#ifndef __MACROS_HPP__
#define __MACROS_HPP__


/** A macro used to disable all default constructors of a class */
#define DELETE_DEFAULTS(X)                                                                        \
    /** Disable default constructor */                                                            \
    X() = delete;                                                                                 \
    /** Disable default copy constructor */                                                       \
    X(const X &) = delete;                                                                        \
    /** Disable default move constructor */                                                       \
    X(X &&) = delete;


#endif
