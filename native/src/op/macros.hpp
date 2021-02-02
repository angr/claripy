/**
 * @file
 * @brief This file defines macros used across the op directory
 */
#ifndef __OP_MACROS_HPP__
#define __OP_MACROS_HPP__

#include "../constants.hpp"
#include "../utils.hpp"


/** Initalize a final op class
 *  Leaves the class in a private access context
 */
#define OP_FINAL_INIT(CLASS)                                                                      \
  public:                                                                                         \
    DEFINE_STATIC_CUID                                                                            \
                                                                                                  \
    /* Delete implicits */                                                                        \
    SET_IMPLICITS_CONST_MEMBERS(CLASS, delete)                                                    \
    /** Default destructor */                                                                     \
    ~CLASS() noexcept override final = default;                                                   \
                                                                                                  \
  private:                                                                                        \
    /** Allow cache friend access                                                                 \
     *  We expose the constructor so that the cache may emplace new objects, which is             \
     *  faster than copying them in                                                               \
     */                                                                                           \
    friend class ::Utils::Cache<Hash::Hash, Base>;


#endif
