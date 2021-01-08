/**
 * @file
 * @brief This file defines the base expression
 */
#ifndef __EXPRESSION_RAW_BASE_HPP__
#define __EXPRESSION_RAW_BASE_HPP__

#include "macros.hpp"


namespace Expression {

    namespace Raw {

        /** The base Expression type
         *  All expressions must subclass this
         */
        struct Base {
            /** Pure virtual destructor */
            virtual ~Base() = 0;
        };

    } // namespace Raw

    // Create a shared pointer alias
    EXPRESSION_RAW_DECLARE_SHARED(Base, Raw)

} // namespace Expression

#endif
