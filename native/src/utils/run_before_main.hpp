/**
 * @file
 * \ingroup utils
 * @brief This file defines a class that will run the function it is passed before main
 */
#ifndef __UTILS_RUNBEFOREMAIN_HPP__
#define __UTILS_RUNBEFOREMAIN_HPP__


/** Define a macro to allow running a literal statement
 *  This must be used outside of a function as it works by declaring global variables
 */
#define UTILS_RUN_STATEMENT_BEFORE_MAIN(STATEMENT)                                                \
    /** Declare an anonomyous namespace to obsure internals  */                                   \
    namespace {                                                                                   \
        /** Declare a class that will run F(args...) before main */                               \
        struct RunBeforeMain {                                                                    \
            /** Constructor */                                                                    \
            RunBeforeMain() { (void) (STATEMENT); }                                               \
            /** Delete copy constructor */                                                        \
            RunBeforeMain(const RunBeforeMain &) = delete;                                        \
            /** Delete move constructor */                                                        \
            RunBeforeMain(RunBeforeMain &&) = delete;                                             \
        };                                                                                        \
        /** Run F(args...) when this object is created */                                         \
        RunBeforeMain rbm;                                                                        \
    }

/** Define a macro to allow running a function before main
 *  This must be used outside of a function as it works by declaring global variables
 */
#define UTILS_RUN_FUNCTION_BEFORE_MAIN(F, ...)                                                    \
    /** Declare an anonomyous namespace to obscure internals */                                   \
    namespace {                                                                                   \
        /** Declare a class that will run F(args...) before main */                               \
        struct RunBeforeMain {                                                                    \
            /** Constructor */                                                                    \
            RunBeforeMain() { (void) F(__VA_ARGS__); }                                            \
            /** Delete copy constructor */                                                        \
            RunBeforeMain(const RunBeforeMain &) = delete;                                        \
            /** Delete move constructor */                                                        \
            RunBeforeMain(RunBeforeMain &&) = delete;                                             \
        };                                                                                        \
        /** Run F(args...) when this object is created */                                         \
        RunBeforeMain rbm;                                                                        \
    }


#endif
