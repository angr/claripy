
/**
 * @file
 * @brief
 */
#ifndef __EXPRESSION_RAW_TYPE_FP_HPP__
#define __EXPRESSION_RAW_TYPE_FP_HPP__

#include "bits.hpp"


namespace Expression::Raw::Type {

    class FP : public Bits {
      public:
        virtual ~FP() = 0;
    };

} // namespace Expression::Raw::Type

#endif
