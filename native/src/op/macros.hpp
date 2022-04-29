/**
 * @file
 * @brief This file defines macros used across the op directory
 */
#ifndef R_SRC_OP_MACROS_HPP_
#define R_SRC_OP_MACROS_HPP_

#include "../constants.hpp"
#include "../unittest.hpp"
#include "../util.hpp"


/** Initialize a non-base pure abstract op class
 *  Leaves the class in a private access context
 *  Note: The constructors for these classes are declared, but not defined
 *  The user must define the destructor as noexcept = default after the class definition
 */
#define OP_PURE_INIT_HELPER(CLASS)                                                                 \
  public:                                                                                          \
    SET_IMPLICITS_CONST_MEMBERS(CLASS, delete);                                                    \
                                                                                                   \
  private:                                                                                         \
    ENABLE_UNITTEST_FRIEND_ACCESS;

/** OP_PURE_INIT_HELPER for the base op class */
#define OP_PURE_INIT_BASE(CLASS)                                                                   \
  public:                                                                                          \
    /** Default destructor */                                                                      \
    virtual inline ~CLASS() noexcept = 0;                                                          \
    OP_PURE_INIT_HELPER(CLASS)

/** OP_PURE_INIT_HELPER for derived op classes */
#define OP_PURE_INIT(CLASS)                                                                        \
  public:                                                                                          \
    /** Default destructor */                                                                      \
    inline ~CLASS() noexcept override = 0;                                                         \
    OP_PURE_INIT_HELPER(CLASS)

/** Initialize a final op class
 *  Leaves the class in a private access context
 *  PREFIX is prepended to the class name
 *  "-" + TARG's value is appended to the class name if TARG is not 0
 */
#define OP_FINAL_INIT(CLASS, PREFIX)                                                               \
  public:                                                                                          \
    /* Delete implicits */                                                                         \
    SET_IMPLICITS_CONST_MEMBERS(CLASS, delete);                                                    \
    /** Default destructor */                                                                      \
    ~CLASS() noexcept final = default;                                                             \
    FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(::Op::Base);                                             \
    /** The name of the op */                                                                      \
    static inline const CCSC static_op_name { PREFIX #CLASS };                                     \
    /** The name of the op */                                                                      \
    inline const char *op_name() const noexcept final {                                            \
        return static_op_name;                                                                     \
    };                                                                                             \
                                                                                                   \
  private:                                                                                         \
    ENABLE_UNITTEST_FRIEND_ACCESS;


#endif
