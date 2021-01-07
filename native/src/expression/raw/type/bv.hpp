
/**
 * @file
 * @brief
 */
#ifndef __EXPRESSION_RAW_TYPE_BV_HPP__
#define __EXPRESSION_RAW_TYPE_BV_HPP__

#include "bits.hpp"


namespace Expression::Raw::Type {

    class BV : public Bits {
      public:
        virtual ~BV() = 0;
    };

} // namespace Expression::Raw::Type

#endif
