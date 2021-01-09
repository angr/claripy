/**
 * @file
 * @brief This file defines a concrete expression
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

            /** Return true if and only if this expression is symbolic */
            bool symbolic() const override final;

          protected:
            /** Disallow public construction */
            Concrete() = default;
        };

    } // namespace Raw

    // Create a shared pointer alias
    EXPRESSION_RAW_DECLARE_SHARED(Concrete, Raw)

} // namespace Expression

#endif
