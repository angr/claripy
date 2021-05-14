/**
 * @file
 * \ingroup utils
 * @brief This file defines a class that will run the function it is passed before main
 */
#ifndef R_UTILS_RUNBEFOREMAIN_HPP_
#define R_UTILS_RUNBEFOREMAIN_HPP_


/** Define a macro to allow running a literal statement
 *  This must be used outside of a function as it works by declaring global variables
 */
#define UTILS_RUN_STATEMENT_BEFORE_MAIN(STATEMENT)                                                \
    /** Declare an anonomyous namespace to obsure internals  */                                   \
    namespace {                                                                                   \
        /** Declare a class that will run F(args...) before main */                               \
        struct [[nodiscard]] RunBeforeMain final {                                                \
            /** Constructor */                                                                    \
            RunBeforeMain() { (void) (STATEMENT); }                                               \
            /** Rule of 5: Destructor */                                                          \
            ~RunBeforeMain() noexcept = default;                                                  \
            /* Disable other creation methods */                                                  \
            SET_IMPLICITS_EXCLUDE_DEFAULT_CTOR(RunBeforeMain, delete)                             \
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
        struct [[nodiscard]] RunBeforeMain final {                                                \
            /** Constructor */                                                                    \
            RunBeforeMain() { (void) F(__VA_ARGS__); }                                            \
            /** Rule of 5: Destructor */                                                          \
            ~RunBeforeMain() noexcept = default;                                                  \
            /* Disable other creation methods */                                                  \
            SET_IMPLICITS_EXCLUDE_DEFAULT_CTOR(RunBeforeMain, delete)                             \
        };                                                                                        \
        /** Run F(args...) when this object is created */                                         \
        RunBeforeMain rbm;                                                                        \
    }


#endif
