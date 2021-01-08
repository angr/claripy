/**
 * @file
 * @brief Macros used across expression raw
 */
#ifndef __EXPRESSION_RAW_MACROS_HPP__
#define __EXPRESSION_RAW_MACROS_HPP__

#include <memory>

/** A macro to declare a shared pointer to X in Expression */
#define EXPRESSION_RAW_DECLARE_SHARED(X, NAMESPACE)                                               \
    /** Declare a shared pointer to X in Expression */                                            \
    using X = std::shared_ptr<NAMESPACE::X>;

#endif
