/**
 * @file
 * @brief
 */
#ifndef __EXPRESSION_RAW_CONCRETE_HPP__
#define __EXPRESSION_RAW_CONCRETE_HPP__

#include "base.hpp"


namespace Expression {

    namespace Raw {

        /** A concrete expression
         *  All concrete expressions must subclass this
         */
        struct Concrete : virtual public Base {
            /** Pure virtual destructor */
            virtual ~Concrete() = 0;
        };

    } // namespace Raw

    // Create a shared pointer alias
    EXPRESSION_RAW_DECLARE_SHARED(Concrete, Raw)

} // namespace Expression

#endif
