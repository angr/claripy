/**
 * @file
 * @brief This file defines a class that has a const size
 */
#ifndef __EXPRESSION_RAW_CUSIZED_HPP__
#define __EXPRESSION_RAW_CUSIZED_HPP__

#include "macros.hpp"

#include "../../constants.hpp"


namespace Expression::Raw {

    /** A class with a const size */
    struct CUSized {
        EXPRESSION_RAW_ABSTRACT_INIT_CUSTOM_CTOR(CUSized)
      public:
        /** The size type */
        using SizeT = Constants::UInt;

        /** The size */
        const SizeT size;

      protected:
        /** Protected constructor */
        CUSized(const SizeT size);
    };

} // namespace Expression::Raw

#endif
