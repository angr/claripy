/**
 * @file
 * \ingroup util
 * @brief This file defines a class that will run the function it is passed after main
 * Warning: This uses the __COUNTER__ macro
 */
#ifndef R_SRC_UTIL_RUNAFTERMAIN_HPP_
#define R_SRC_UTIL_RUNAFTERMAIN_HPP_

#include "../macros.hpp"


// Verify counter is supported
static_assert(((__COUNTER__ + 1) == __COUNTER__) && ((__COUNTER__ + 2) != __COUNTER__),
              "Counter not supported");


/** Define a macro to allow running a literal statement
 *  This must be used outside of a function as it works by declaring global variables
 */
#define UTIL_RUN_STATEMENT_AFTER_MAIN(STATEMENT)                                                   \
    /** Declare an anonymous namespace to obscure internals  */                                    \
    namespace MACRO_CONCAT(__RAM_, __COUNTER__) {                                                  \
        /** Declare a class that will run F(args...) before main */                                \
        struct [[nodiscard]] RunAfterMain final {                                                  \
            /** Default constructor */                                                             \
            RunAfterMain() noexcept = default;                                                     \
            /** Destructor */                                                                      \
            ~RunAfterMain() { (void) (STATEMENT); }                                                \
            /* Disable non-default creation methods */                                             \
            SET_IMPLICITS_EXCLUDE_DEFAULT_CTOR(RunAfterMain, delete)                               \
        };                                                                                         \
        /** Run F(args...) when this object is created */                                          \
        static RunAfterMain ram;                                                                   \
    }

/** Define a macro to allow running a function before main
 *  This must be used outside of a function as it works by declaring global variables
 */
#define UTIL_RUN_FUNCTION_AFTER_MAIN(F, ...)                                                       \
    /** Declare an anonymous namespace to obscure internals */                                     \
    namespace MACRO_CONCAT(__RAM_, __COUNTER__) {                                                  \
        /** Declare a class that will run F(args...) before main */                                \
        struct [[nodiscard]] RunAfterMain final {                                                  \
            /** Default constructor */                                                             \
            RunAfterMain() noexcept = default;                                                     \
            /** Destructor */                                                                      \
            ~RunAfterMain() { (void) (F) (__VA_ARGS__); }                                          \
            /* Disable non-default creation methods */                                             \
            SET_IMPLICITS_EXCLUDE_DEFAULT_CTOR(RunAfterMain, delete)                               \
        };                                                                                         \
        /** Run F(args...) when this object is created */                                          \
        static RunAfterMain ram;                                                                   \
    }


#endif
