/**
 * @file
 * @brief This file defines macros used across the op directory
 */
#ifndef R_OP_MACROS_HPP_
#define R_OP_MACROS_HPP_

#include "../constants.hpp"
#include "../unittest.hpp"
#include "../utils.hpp"


/** Initialize a non-base pure abstract op class
 *  Leaves the class in a private access context
 *  Note: The constructors for these classes are declared, but not defined
 *  The user must define the destructor as noexcept = default after the class definition
 */
#define OP_PURE_INIT(CLASS)                                                                       \
  public:                                                                                         \
    /* Delete implicits */                                                                        \
    SET_IMPLICITS_CONST_MEMBERS(CLASS, delete);                                                   \
    /** Default destructor */                                                                     \
    inline ~CLASS() noexcept override = 0;                                                        \
                                                                                                  \
  private:                                                                                        \
    ENABLE_UNITTEST_FRIEND_ACCESS;

/** Initialize a final op class
 *  Leaves the class in a private access context
 *  Optionally pass a second argument to prefix the class name for the debug name
 *  X can be anything, but must be different between different templates of the same class
 *  For example, Foo<int> must give a different X from Foo<bool>
 */
#define OP_FINAL_INIT(CLASS, X, ...)                                                              \
  public:                                                                                         \
    /* Delete implicits */                                                                        \
    SET_IMPLICITS_CONST_MEMBERS(CLASS, delete);                                                   \
    /** Default destructor */                                                                     \
    ~CLASS() noexcept override final = default;                                                   \
    FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(::Op::Base, (X));                                       \
    /** The name of the op */                                                                     \
    inline const char *op_name() const noexcept override final { return __VA_ARGS__ #CLASS; };    \
                                                                                                  \
  private:                                                                                        \
    ENABLE_UNITTEST_FRIEND_ACCESS;


#endif
