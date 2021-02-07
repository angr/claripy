/**
 * @file
 * @brief Define simplifiers in Simplifications::Simplifier
 */
#ifndef __SIMPLIFICATION_SIMPLIFIERS_HPP__
#define __SIMPLIFICATION_SIMPLIFIERS_HPP__

#include "constants.hpp"


namespace Simplification::Simplifier {

    /************************************************/
    /*                 Miscellaneous                */
    /************************************************/

    /** Return if_true, if_false, or original depending on what cond evaluates to */
    SimplifierFunc if_;

    /** @todo document */
    SimplifierFunc concat;

    namespace BV {

        /** @todo document */
        SimplifierFunc reverse;

    } // namespace BV

    /************************************************/
    /*                    Shift                     */
    /************************************************/

    namespace Shift {

        /** @todo document */
        SimplifierFunc r;

        /** @todo document */
        SimplifierFunc l;

        /** @todo document */
        SimplifierFunc lshr;

    } // namespace Shift

    /************************************************/
    /*                   Equality                   */
    /************************************************/

    /** @todo document */
    SimplifierFunc eq;

    /** @todo document */
    SimplifierFunc ne;

    /************************************************/
    /*                   Boolean                    */
    /************************************************/

    namespace Boolean {

        /** @todo document */
        SimplifierFunc and_;

        /** @todo document */
        SimplifierFunc or_;

        /** @todo document */
        SimplifierFunc not_;

    } // namespace Boolean

    /************************************************/
    /*                   Bitwise                    */
    /************************************************/

    namespace Bitwise {

        /** @todo document */
        SimplifierFunc add;

        /** @todo document */
        SimplifierFunc mul;

        /** @todo document */
        SimplifierFunc sub;

        /** @todo document */
        SimplifierFunc xor_minmax;

        /** @todo document */
        SimplifierFunc or_;

        /** @todo document */
        SimplifierFunc and_;

        /** @todo document */
        SimplifierFunc xor_;

    } // namespace Bitwise

} // namespace Simplification::Simplifier

#endif
