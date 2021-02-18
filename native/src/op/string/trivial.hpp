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

    /** The unary string op class: String::IsDigit */
    OP_UNARY_TRIVIAL_SUBCLASS(IsDigit);

    /** The unary string op class: String::FromInt */
    OP_UNARY_TRIVIAL_SUBCLASS(FromInt);

    /** The unary string op class: String::Unit */
    OP_UNARY_TRIVIAL_SUBCLASS(Unit);

    /**********************************************************/
    /*                   Binary Subclasses                    */
    /**********************************************************/

    /** The string binary op class: String::Contains
     *  Input sizes may differ
     */
    OP_BINARY_TRIVIAL_SUBCLASS(Contains, false);

    /** The string binary op class: String::PrefixOf
     *  Input sizes may differ
     */
    OP_BINARY_TRIVIAL_SUBCLASS(PrefixOf, false);

    /** The string binary op class: String::SuffixOf
     *  Input sizes may differ
     */
    OP_BINARY_TRIVIAL_SUBCLASS(SuffixOf, false);

    /**********************************************************/
    /*                   Ternary Subclasses                   */
    /**********************************************************/

    /** The ternary string op class: String::Replace
     *  Input sizes may differ
     */
    OP_TERNARY_TRIVIAL_SUBCLASS(Replace, false);

} // namespace Op::String

#endif
