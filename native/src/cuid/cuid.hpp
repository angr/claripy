/**
 * @file
 * @brief This file defines a class unique identifier type
 * This also defined a type that has a unique class id
 * This file also defines macros to create a static_cuid
 */
#ifndef R_SRC_CUID_CUID_HPP_
#define R_SRC_CUID_CUID_HPP_

#include "../constants.hpp"
#include "../macros.hpp"
#include "../util.hpp"

/** Used to define a possibly unused static_cuid in a class
 *  Leaves the class in a public state
 *  Will not cause any compiler warnings if this field is not used
 *  X should be trivial to convert to a U64
 *  For example, Foo<int> must give a different X than Foo<bool> gives
 */
#define CUID_DEFINE_MAYBE_UNUSED(X)                                                                \
  public:                                                                                          \
    /** Define a static_cuid */                                                                    \
    [[maybe_unused]] static const constexpr ::CUID::CUID static_cuid {                             \
        UTIL_FILE_LINE_HASH ^ Util::FNV1a<U64>::hash(Util::to_u_ptr<X>(), 1)                       \
    };

namespace CUID {

    /** The CUID type */
    using CUID = U64;

    /** A type that has a class unique id
     *  This has the benefits of a virtual function as inherited classes
     *  can have different CUIDs than their ancestors, while also avoiding
     *  the overhead of a vtabel call to invoke virtual cuid() const;
     *  Warning: No virtual destructor; do *not* delete by base class pointer; avoid slicing!
     */
    struct HasCUID {
        /** Constructor */
        inline HasCUID(const CUID &c) noexcept : cuid { c } {}
        /** The class unique id */
        const CUID cuid;
    };

} // namespace CUID

#endif
