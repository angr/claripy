/**
 * @file
 * @brief
 */
#ifndef __EXPRESSION_RAW_OP_IF_HPP__
#define __EXPRESSION_RAW_OP_IF_HPP__

#include "base.hpp"


namespace Expression::Raw::Op {

    class If : public Base {
      public:
        virtual ~If() = 0;
    };

} // namespace Expression::Raw::Op

#endif
