/**
 * @file
 * @brief
 */
#ifndef __EXPRESSION_RAW_SYMBOLIC_HPP__
#define __EXPRESSION_RAW_SYMBOLIC_HPP__

#include "base.hpp"


namespace Expression {

    namespace Raw {

        /** A symbolic expression
         *  All symbolic expressions must subclass this
         */

        struct Symbolic : virtual public Base {
            /** Pure virtual destructor */
            virtual ~Symbolic() = 0;
        };

    } // namespace Raw

    // Create a shared pointer alias
    EXPRESSION_RAW_DECLARE_SHARED(Symbolic, Raw)

} // namespace Expression

#endif
