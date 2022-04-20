/**
 * @file
 * @brief Define trivial string subclass ops
 */
#ifndef R_SRC_OP_STRING_TRIVIAL_HPP_
#define R_SRC_OP_STRING_TRIVIAL_HPP_

#include "../binary.hpp"
#include "../ternary.hpp"
#include "../uint_binary.hpp"
#include "../unary.hpp"


namespace Op::String {

    /**********************************************************/
    /*                    Unary Subclasses                    */
    /**********************************************************/

    /** The unary string op class: String::IsDigit */
    OP_UNARY_TRIVIAL_SUBCLASS(IsDigit, "String::", 0);

    /** The unary string op class: String::FromInt */
    OP_UNARY_TRIVIAL_SUBCLASS(FromInt, "String::", 0);

    /**********************************************************/
    /*                  UIntBinary Subclasses                 */
    /**********************************************************/

    /** The int binary op class: String::ToInt */
    OP_UINTBINARY_TRIVIAL_SUBCLASS(ToInt, "String::", 0);

    /** The int binary op class: String::Len */
    OP_UINTBINARY_TRIVIAL_SUBCLASS(Len, "String::", 0);

    /**********************************************************/
    /*                   Binary Subclasses                    */
    /**********************************************************/

    /** The string binary op class: String::Contains
     *  Input sizes may differ
     */
    OP_BINARY_TRIVIAL_SUBCLASS(Contains, false, "String::", 0);

    /** The string binary op class: String::PrefixOf
     *  Input sizes may differ
     */
    OP_BINARY_TRIVIAL_SUBCLASS(PrefixOf, false, "String::", 0);

    /** The string binary op class: String::SuffixOf
     *  Input sizes may differ
     */
    OP_BINARY_TRIVIAL_SUBCLASS(SuffixOf, false, "String::", 0);

    /**********************************************************/
    /*                   Ternary Subclasses                   */
    /**********************************************************/

    /** The ternary string op class: String::Replace
     *  Input sizes may differ
     */
    OP_TERNARY_TRIVIAL_SUBCLASS(Replace, false, "String::", 0);

} // namespace Op::String

#endif
