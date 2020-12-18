/**
 * @file
 * @brief This file contains macros used across ast
 */
#ifndef __AST_MACROS_HPP__
#define __AST_MACROS_HPP__


/** Used to define the using statement that obscures AST raw types */
#define DEFINE_NON_RAW_TYPE(RAW)                                                                  \
    /** An abbreviation for a shared pointer to the cached RAW class */                           \
    using RAW = std::shared_ptr<RawTypes::RAW>;


#endif
