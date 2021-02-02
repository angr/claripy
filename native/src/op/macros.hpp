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
    /** Static check */                                                                           \
    static_assert(std::is_final_v<CLASS>, #CLASS " must be final");                               \
                                                                                                  \
    /* Delete implicits */                                                                        \
    SET_IMPLICITS_CONST_MEMBERS(CUID, delete)                                                     \
    /** Default destructor */                                                                     \
    ~CLASS() noexcept override final = default;                                                   \
                                                                                                  \
    /** Create class unique id */                                                                 \
    static const constexpr Constants::UInt class_uid { UTILS_FILE_LINE_HASH };                    \
                                                                                                  \
  private:


#endif
