/**
 * @file
 * @brief This file contains macros used across ast
 */
#ifndef __EXPRESSION_MACROS_HPP__
#define __EXPRESSION_MACROS_HPP__


/** Used to define the using statement that obscures Expression raw types
 *  This should be called only when within the Expression namespace
 */
#define EXPRESSION_DECLARE_AND_DEFINE_NON_RAW_TYPE(RAW)                                           \
    /** An abbreviation for a shared pointer to the cached RAW class */                           \
    using RAW = std::shared_ptr<Raw::Type::RAW>;

/** Used to define the using statement that obscures Expression raw types
 *  This should be called only when not in any namespace
 */
#define EXPRESSION_DECLARE_AND_DEFINE_NON_RAW_TYPE_FROM_GLOBAL(RAW)                               \
    namespace Expression {                                                                        \
        EXPRESSION_DECLARE_AND_DEFINE_NON_RAW_TYPE(RAW)                                           \
    }

#endif
