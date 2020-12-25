/**
 * @file
 * @brief Define simplifiers in Simplifications::Simplifiers
 */
#ifndef __SIMPLIFICATIONS_SIMPLIFIERS_HPP__
#define __SIMPLIFICATIONS_SIMPLIFIERS_HPP__

#include "constants.hpp"

#include "../ops/operations_enum.hpp"


namespace Simplifications::Simplifiers {

    /************************************************/
    /*                 Miscellaneous                */
    /************************************************/

    /** Return if_true, if_false, or original depending on what cond evaluates to */
    Simplifier if_;

    /** @todo document */
    Simplifier concat;

    namespace BV {

        /** @todo document */
        Simplifier reverse;

    } // namespace BV

    /************************************************/
    /*                    Shift                     */
    /************************************************/

    namespace Shift {

        /** @todo document */
        Simplifier r;

        /** @todo document */
        Simplifier l;

        /** @todo document */
        Simplifier lshr;

    } // namespace Shift

    /************************************************/
    /*                   Equality                   */
    /************************************************/

    /** @todo document */
    Simplifier eq;

    /** @todo document */
    Simplifier ne;

    /************************************************/
    /*                   Boolean                    */
    /************************************************/

    namespace Boolean {

        /** @todo document */
        Simplifier and_;

        /** @todo document */
        Simplifier or_;

        /** @todo document */
        Simplifier not_;

    } // namespace Boolean

    /************************************************/
    /*                   Bitwise                    */
    /************************************************/

    namespace Bitwise {

        /** @todo document */
        Simplifier add;

        /** @todo document */
        Simplifier mul;

        /** @todo document */
        Simplifier sub;

        /** @todo document */
        Simplifier xor_minmax;

        /** @todo document */
        Simplifier or_;

        /** @todo document */
        Simplifier and_;

        /** @todo document */
        Simplifier xor_;

    } // namespace Bitwise

} // namespace Simplifications::Simplifiers

#endif
