/**
 * @file
 * @brief This file defines a type that has a unique class id
 */
#ifndef __FACTORY_CUID_HPP__
#define __FACTORY_CUID_HPP__

#include "../constants.hpp"
#include "../macros.hpp"


namespace Factory {

    /** A type that has a class unique id
     *  This has the benefits of a virtual function as inhereted classes
     *  can have different CUIDs than their ancestors, while also avoiding
     *  the overhead of a vtabel call to invoke virtual cuid() const;
     *  Note: factory only requires static_cuid be defined, subclassing
     *  from this class is not mandatory, however, it is useful if one
     *  desires to access cuid from a dynamically typed context
     */
    struct CUID {

        /** The class unique id */
        const Constants::UInt cuid;

      protected:
        /** Constructor */
        explicit inline CUID(const Constants::UInt c) noexcept : cuid { c } {}

        /** Virtual destructor */
        virtual inline ~CUID() noexcept;

        // Rule of 5
        SET_IMPLICITS_CONST_MEMBERS(CUID, default, noexcept)
    };

    /** Default virtual destructor */
    CUID::~CUID() noexcept = default;

} // namespace Factory

#endif
