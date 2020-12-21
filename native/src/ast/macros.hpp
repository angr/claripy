/**
 * @file
 * @brief This file contains macros used across ast
 */
#ifndef __AST_MACROS_HPP__
#define __AST_MACROS_HPP__


/** Used to define the using statement that obscures AST raw types
 *  This should be called only when within the AST namespace
 */
#define AST_DECLARE_AND_DEFINE_NON_RAW_TYPE(RAW)                                                  \
    /** An abbreviation for a shared pointer to the cached RAW class */                           \
    using RAW = std::shared_ptr<RawTypes::RAW>;

/** Used to define the using statement that obscures AST raw types
 *  This should be called only when not in any namespace
 */
#define AST_DECLARE_AND_DEFINE_NON_RAW_TYPE_FROM_GLOBAL(RAW)                                      \
    /** A namespace used for the ast directory */                                                 \
    namespace AST {                                                                               \
        AST_DECLARE_AND_DEFINE_NON_RAW_TYPE(RAW)                                                  \
    }

#endif
