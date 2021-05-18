/**
 * @file
 * \ingroup utils
 * @brief This file defines a class that will run the function it is passed after main
 * Note: This might not run if an exception terminates main
 */
#ifndef R_UTILS_RUNAFTERMAIN_HPP_
#define R_UTILS_RUNAFTERMAIN_HPP_


/** Define a macro to allow running a literal statement
 *  This must be used outside of a function as it works by declaring global variables
 */
#define UTILS_RUN_STATEMENT_AFTER_MAIN(STATEMENT)                                                 \
    /** Declare an anonomyous namespace to obsure internals  */                                   \
    namespace {                                                                                   \
        /** Declare a class that will run F(args...) before main */                               \
        struct [[nodiscard]] RunAfterMain final {                                                 \
            /** Default constructor */                                                            \
            RunAfterMain() noexcept = default;                                                    \
            /** Destructor */                                                                     \
            ~RunAfterMain() { (void) (STATEMENT); }                                               \
            /* Disable non-default creation methods */                                            \
            SET_IMPLICITS_EXCLUDE_DEFAULT_CTOR(RunAfterMain, delete)                              \
        };                                                                                        \
        /** Run F(args...) when this object is created */                                         \
        RunAfterMain ram;                                                                         \
    }

/** Define a macro to allow running a function before main
 *  This must be used outside of a function as it works by declaring global variables
 */
#define UTILS_RUN_FUNCTION_AFTER_MAIN(F, ...)                                                     \
    /** Declare an anonomyous namespace to obscure internals */                                   \
    namespace {                                                                                   \
        /** Declare a class that will run F(args...) before main */                               \
        struct [[nodiscard]] RunAfterMain final {                                                 \
            /** Default constructor */                                                            \
            RunAfterMain() noexcept = default;                                                    \
            /** Destructor */                                                                     \
            ~RunAfterMain() { (void) (F)(__VA_ARGS__); }                                          \
            /* Disable non-default creation methods */                                            \
            SET_IMPLICITS_EXCLUDE_DEFAULT_CTOR(RunAfterMain, delete)                              \
        };                                                                                        \
        /** Run F(args...) when this object is created */                                         \
        RunAfterMain ram;                                                                         \
    }


#endif
