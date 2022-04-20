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
#define OP_PURE_INIT(CLASS)                                                                        \
  public:                                                                                          \
    /* Delete implicits */                                                                         \
    SET_IMPLICITS_CONST_MEMBERS(CLASS, delete);                                                    \
    /** Default destructor */                                                                      \
    inline ~CLASS() noexcept override = 0;                                                         \
                                                                                                   \
  private:                                                                                         \
    ENABLE_UNITTEST_FRIEND_ACCESS;

namespace Op::Private {
    /** A helper for OP_FINAL_INIT */
    template <typename T> const char *str(CCSC head, T tail) {
        if constexpr (std::is_convertible_v<T, U64>) {
            if (tail == 0) {
                return head;
            }
        }
        return Util::to_c_str(head, '-', std::forward<T>(tail));
    }
} // namespace Op::Private

/** Initialize a final op class
 *  Leaves the class in a private access context
 *  PREFIX is prepended to the class name
 *  "-" + TARG's value is appended to the class name if TARG is not 0
 *  TARG also must be different between templates
 *  For example, Foo<int> must give a different TARG from Foo<bool>
 */
#define OP_FINAL_INIT(CLASS, PREFIX, TARG)                                                         \
  public:                                                                                          \
    /* Delete implicits */                                                                         \
    SET_IMPLICITS_CONST_MEMBERS(CLASS, delete);                                                    \
    /** Default destructor */                                                                      \
    ~CLASS() noexcept final = default;                                                             \
    FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(::Op::Base, TARG);                                       \
    /** The name of the op */                                                                      \
    static inline const CCSC static_op_name { ::Op::Private::str(PREFIX #CLASS, TARG) };           \
    /** The name of the op */                                                                      \
    inline const char *op_name() const noexcept final {                                            \
        return static_op_name;                                                                     \
    };                                                                                             \
                                                                                                   \
  private:                                                                                         \
    ENABLE_UNITTEST_FRIEND_ACCESS;


#endif
