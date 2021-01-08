/**
 * @file
 * @brief Expose all relevant public members of type
 */
#ifndef __EXPRESSION_RAW_TYPE_HPP__
#define __EXPRESSION_RAW_TYPE_HPP__

#include "macros.hpp"
#include "type/base.hpp"
#include "type/bits.hpp"
#include "type/bool.hpp"
#include "type/bv.hpp"
#include "type/fp.hpp"
#include "type/int.hpp"
#include "type/string.hpp"
#include "type/vs.hpp"

#include <memory>

namespace Expression {

    // Declare shared pointers types
    EXPRESSION_RAW_DECLARE_SHARED(Base, Raw::Type)
    EXPRESSION_RAW_DECLARE_SHARED(Bits, Raw::Type)
    EXPRESSION_RAW_DECLARE_SHARED(Bool, Raw::Type)
    EXPRESSION_RAW_DECLARE_SHARED(Int, Raw::Type)
    EXPRESSION_RAW_DECLARE_SHARED(String, Raw::Type)
    EXPRESSION_RAW_DECLARE_SHARED(FP, Raw::Type)
    EXPRESSION_RAW_DECLARE_SHARED(BV, Raw::Type)
    EXPRESSION_RAW_DECLARE_SHARED(VS, Raw::Type)

} // namespace Expression

#endif
