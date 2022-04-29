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
    OP_UNARY_TRIVIAL_SUBCLASS(IsDigit, "String::");

    /** The unary string op class: String::FromInt */
    OP_UNARY_TRIVIAL_SUBCLASS(FromInt, "String::");

    /**********************************************************/
    /*                  UIntBinary Subclasses                 */
    /**********************************************************/

    /** The int binary op class: String::ToInt */
    OP_UINTBINARY_TRIVIAL_SUBCLASS(ToInt, "String::");

    /** The int binary op class: String::Len */
    OP_UINTBINARY_TRIVIAL_SUBCLASS(Len, "String::");

    /**********************************************************/
    /*                   Binary Subclasses                    */
    /**********************************************************/

    /** The string binary op class: String::Contains
     *  Input sizes may differ
     */
    OP_BINARY_TRIVIAL_FINAL_DESCENDANT(Contains, Binary<false>, "String::");

    /** The string binary op class: String::PrefixOf
     *  Input sizes may differ
     */
    OP_BINARY_TRIVIAL_FINAL_DESCENDANT(PrefixOf, Binary<false>, "String::");

    /** The string binary op class: String::SuffixOf
     *  Input sizes may differ
     */
    OP_BINARY_TRIVIAL_FINAL_DESCENDANT(SuffixOf, Binary<false>, "String::");

    /**********************************************************/
    /*                   Ternary Subclasses                   */
    /**********************************************************/

    /** The ternary string op class: String::Replace
     *  Input sizes may differ
     */
    OP_TERNARY_TRIVIAL_SUBCLASS(Replace, false, "String::");

} // namespace Op::String

#endif
