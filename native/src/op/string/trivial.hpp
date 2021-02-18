/**
 * @file
 * @brief Define trivial string subclass ops
 */
#ifndef __OP_STRING_TRIVIAL_HPP__
#define __OP_STRING_TRIVIAL_HPP__

#include "../binary.hpp"
#include "../ternary.hpp"
#include "../unary.hpp"


namespace Op::String {

    /**********************************************************/
    /*                    Unary Subclasses                    */
    /**********************************************************/

    /** The unary string op class: IsDigit */
    OP_UNARY_TRIVIAL_SUBCLASS(IsDigit);

    /**********************************************************/
    /*                   Binary Subclasses                    */
    /**********************************************************/

    /** The string binary op class: Contains
     *  Input sizes may differ
     */
    OP_BINARY_TRIVIAL_SUBCLASS(Contains, false);

    /** The string binary op class: PrefixOf
     *  Input sizes may differ
     */
    OP_BINARY_TRIVIAL_SUBCLASS(PrefixOf, false);

    /** The string binary op class: SuffixOf
     *  Input sizes may differ
     */
    OP_BINARY_TRIVIAL_SUBCLASS(SuffixOf, false);

    /**********************************************************/
    /*                   Ternary Subclasses                   */
    /**********************************************************/

    /** The ternary string op class: Replace
     *  Input sizes may differ
     */
    OP_TERNARY_TRIVIAL_SUBCLASS(Replace, false);

} // namespace Op::String

#endif
