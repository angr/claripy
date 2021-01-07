/**
 * @file
 * @brief
 */
#ifndef __EXPRESSION_RAW_TYPE_BOOL_HPP__
#define __EXPRESSION_RAW_TYPE_BOOL_HPP__

#include "../base.hpp"


namespace Expression::Raw::Type {

    class Bool : public Base {
      public:
        virtual ~Bool() = 0;
    };

} // namespace Expression::Raw::Type

#endif
