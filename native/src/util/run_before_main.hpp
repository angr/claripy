/**
 * @file
 * \ingroup util
 * @brief This file defines a class that will run the function it is passed before main
 * Warning: This uses the __COUNTER__ macro
 */
#ifndef R_UTIL_RUNBEFOREMAIN_HPP_
#define R_UTIL_RUNBEFOREMAIN_HPP_

#include "../macros.hpp"


/** Define a macro to allow running a literal statement
 *  This must be used outside of a function as it works by declaring global variables
 */
#define UTILS_RUN_STATEMENT_BEFORE_MAIN(STATEMENT)                                                 \
    /** Declare an anonymous namespace to obscure internals  */                                    \
    namespace MACRO_CONCAT(__RBM_, __COUNTER__) {                                                  \
        /** Declare a class that will run F(args...) before main */                                \
        struct [[nodiscard]] RunBeforeMain final {                                                 \
            /** Constructor */                                                                     \
            RunBeforeMain() { (void) (STATEMENT); }                                                \
            /** Rule of 5: Destructor */                                                           \
            ~RunBeforeMain() noexcept = default;                                                   \
            /* Disable other creation methods */                                                   \
            SET_IMPLICITS_EXCLUDE_DEFAULT_CTOR(RunBeforeMain, delete)                              \
        };                                                                                         \
        /** Run F(args...) when this object is created */                                          \
        static RunBeforeMain rbm;                                                                  \
    }

/** Define a macro to allow running a function before main
 *  This must be used outside of a function as it works by declaring global variables
 */
#define UTILS_RUN_FUNCTION_BEFORE_MAIN(F, ...)                                                     \
    /** Declare an anonymous namespace to obscure internals */                                     \
    namespace MACRO_CONCAT(__RBM_, __COUNTER__) {                                                  \
        /** Declare a class that will run F(args...) before main */                                \
        struct [[nodiscard]] RunBeforeMain final {                                                 \
            /** Constructor */                                                                     \
            RunBeforeMain() { (void) (F)(__VA_ARGS__); }                                           \
            /** Rule of 5: Destructor */                                                           \
            ~RunBeforeMain() noexcept = default;                                                   \
            /* Disable other creation methods */                                                   \
            SET_IMPLICITS_EXCLUDE_DEFAULT_CTOR(RunBeforeMain, delete)                              \
        };                                                                                         \
        /** Run F(args...) when this object is created */                                          \
        static RunBeforeMain rbm;                                                                  \
    }


#endif
