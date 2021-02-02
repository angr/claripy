/**
 * @file
 * @brief This defines macros used across SOC
 */
#ifndef __SOC_MACROS_HPP__
#define __SOC_MACROS_HPP__

#include "../cuid.hpp"
#include "../utils.hpp"


/** Allows factor construction of final types */
#define SOC_FINAL_INIT                                                                            \
    DEFINE_STATIC_CUID                                                                            \
    /** Allow cache friend access                                                                 \
     *  We expose the constructor so that the cache may emplace new objects, which is             \
     *  faster than copying them in                                                               \
     */                                                                                           \
    friend class ::Utils::Cache<Hash::Hash, Base>;


#endif
