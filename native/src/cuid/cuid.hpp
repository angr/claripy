/**
 * @file
 * @brief This file defines a class unique identifier type
 * This also defined a type that has a unique class id
 * This file also defines macros to create a static_cuid
 */
#ifndef __CUID_CUID_HPP__
#define __CUID_CUID_HPP__

#include "../constants.hpp"
#include "../macros.hpp"
#include "../utils.hpp"


/** Used to define a possible unused static_cuid in a class
 *  Leaves the class in a public state
 *  Will not cause any compiler warnings if this field is not used
 *  X can be anything, but must be different between different templates of the same class
 *  For example, Foo<int> must give a different X from Foo<bool>
 */
#define CUID_DEFINE_MAYBE_UNUSED(X)                                                               \
  public:                                                                                         \
    /** Define a static_cuid */                                                                   \
    [[maybe_unused]] static const constexpr ::CUID::CUID static_cuid { UTILS_FILE_LINE_HASH ^     \
                                                                       (X) };


namespace CUID {

    /** The CUID type */
    using CUID = Constants::UInt;

    /** A type that has a class unique id
     *  This has the benefits of a virtual function as inhereted classes
     *  can have different CUIDs than their ancestors, while also avoiding
     *  the overhead of a vtabel call to invoke virtual cuid() const;
     */
    struct HasCUID {

        /** The class unique id */
        const CUID cuid;

      protected:
        /** Constructor */
        explicit constexpr HasCUID(const CUID &c) noexcept : cuid { c } {}

        /** Pure virtual destructor */
        virtual inline ~HasCUID() noexcept = 0;

        // Rule of 5
        SET_IMPLICITS_CONST_MEMBERS(HasCUID, default, noexcept)
    };

    /** Default virtual destructor */
    HasCUID::~HasCUID() noexcept = default;

} // namespace CUID

#endif
