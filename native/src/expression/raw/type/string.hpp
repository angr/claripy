
/**
 * @file
 * @brief
 */
#ifndef __EXPRESSION_RAW_TYPE_STRING_HPP__
#define __EXPRESSION_RAW_TYPE_STRING_HPP__

#include "bits.hpp"


namespace Expression::Raw::Type {

    class String : public Bits {
      public:
        virtual ~String() = 0;
    };

} // namespace Expression::Raw::Type

#endif
