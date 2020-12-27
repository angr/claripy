/**
 * @file
 * @brief This file defines a class that will run the function it is passed before main
 */
#ifndef __UTILS_RUNBEFOREMAIN_HPP__
#define __UTILS_RUNBEFOREMAIN_HPP__

#include "private/run_function.hpp"


/** Define a macro to allow running a literal statement
 *  This must be used outside of a function as it works by declaring global variables
 */
#define UTILS_RUN_STATEMENT_BEFORE_MAIN(STATEMENT)                                                \
    /** Declare an anonomyous namespace */                                                        \
    namespace {                                                                                   \
        /** Declare a class that will run F(args...) before main */                               \
        struct RunBeforeMain {                                                                    \
            RunBeforeMain() { (void) STATEMENT; }                                                 \
        };                                                                                        \
        /** Run F(args...) when this object is created */                                         \
        RunBeforeMain rbm;                                                                        \
    }

/** Define a macro to allow running a function before main
 *  This must be used outside of a function as it works by declaring global variables
 */
#define UTILS_RUN_FUNCTION_BEFORE_MAIN(F, ...)                                                    \
    /** Declare an anonomyous namespace */                                                        \
    namespace {                                                                                   \
        /** Declare a class that will run F(args...) before main */                               \
        struct RunBeforeMain {                                                                    \
            RunBeforeMain() { (void) Utils::Private::run_function(F, __VA_ARGS__); }              \
        };                                                                                        \
        /** Run F(args...) when this object is created */                                         \
        RunBeforeMain rbm;                                                                        \
    }


#endif
