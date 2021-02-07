/**
 * @file
 * @brief This file contains the possible Expression exceptions claricpp can raise
 * These exceptions have python analogs and must be caught and set to python
 * via a different method.
 * @todo Document method when known
 */
#ifndef __ERROR_EXPRESSION_HPP__
#define __ERROR_EXPRESSION_HPP__

#include "../utils.hpp"


namespace Error {

    // Expression errors
    namespace Expression {

        /** Base Expression exception
         *  All Expression exceptions must derive from this
         */
        struct Base : public Utils::Error::Claricpp {

            /** Inherit constructors */
            using Claricpp::Claricpp;

            /** Virtual destructor */
            inline virtual ~Base() noexcept = default;
        };

        // Intermediate classes

        /** Expression Balance exception */
        struct Balancer : public Base {

            /** Inherit constructors */
            using Base::Base;

            /** Virtual destructor */
            inline virtual ~Balancer() noexcept = default;
        };

        /** Expression Balance exception */
        struct Operator : public Base {

            /** Inherit constructors */
            using Base::Base;

            /** Virtual destructor */
            inline virtual ~Operation() noexcept = default;
        };

        // Final classes

        /** @todo document */
        DEFINE_FINAL_SUBCLASS_WITH_CTOR(BalancerUnsat, Balancer)
        /** @todo document */
        DEFINE_FINAL_SUBCLASS_WITH_CTOR(Type, Base)
        /** @todo document */
        DEFINE_FINAL_SUBCLASS_WITH_CTOR(Value, Base)
        /** @todo document */
        DEFINE_FINAL_SUBCLASS_WITH_CTOR(Size, Base)
        /** @todo document */
        DEFINE_FINAL_SUBCLASS_WITH_CTOR(Replacement, Base)
        /** @todo document */
        DEFINE_FINAL_SUBCLASS_WITH_CTOR(Recursion, Operation)
        /** @todo document */
        DEFINE_FINAL_SUBCLASS_WITH_CTOR(ZeroDivision, Operation)

    } // namespace Expression

} // namespace Error

#endif
