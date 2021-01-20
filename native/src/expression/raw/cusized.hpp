/**
 * @file
 * @brief This file defines a class that has a const size
 */
#ifndef __EXPRESSION_RAW_CUSIZED_HPP__
#define __EXPRESSION_RAW_CUSIZED_HPP__

#include "../../constants.hpp"
#include "../../macros.hpp"


namespace Expression::Raw {

    /** A class with a const size */
    struct CUSized {
        DELETE_DEFAULTS(CUSized)

        /** The size type */
        using SizeT = Constants::UInt;

        /** Constructor */
        CUSized(const SizeT size);

        /** Pure virtual destructor */
        virtual ~CUSized() = 0;

        /** The size */
        const SizeT size;
    };

} // namespace Expression::Raw

#endif
