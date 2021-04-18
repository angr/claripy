/**
 * @file
 * @brief This file defines the String::IndexOf class
 */
#ifndef __OP_STRING_INDEXOF_HPP__
#define __OP_STRING_INDEXOF_HPP__

#include "../base.hpp"


namespace Op::String {

    /** The op class: String::IndexOf */
    class IndexOf final : public Base {
        OP_FINAL_INIT(IndexOf, "String::");

      public:
        /** String to search: This must be an Expression::String pointer
         *  Note: We leave it as a base for optimizations purposes
         */
        const Expression::BasePtr str;
        /** Pattern to search for: This must be an Expression::String pointer
         *  Note: We leave it as a base for optimizations purposes
         */
        const Expression::BasePtr pattern;
        /** Start Index
         *  Note: We leave it as a base for optimizations purposes
         */
        const Expression::BasePtr start_index;

        /** Add's the raw expression children of the expression to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        inline void add_reversed_children(Stack &s) const override final {
            s.emplace(start_index.get());
            s.emplace(pattern.get());
            s.emplace(str.get());
        }

      private:
        /** Protected constructor
         *  Ensure that str and pattern are of type String
         */
        explicit inline IndexOf(const Hash::Hash &h, const Expression::BasePtr &s,
                                const Expression::BasePtr &pat, const Expression::BasePtr &si)
            : Base { h, static_cuid }, str { s }, pattern { pat }, start_index { si } {
            using Err = Error::Expression::Type;
            Utils::affirm<Err>(CUID::is_t<Expression::String>(str),
                               WHOAMI_WITH_SOURCE "str expression must be a String");
            Utils::affirm<Err>(CUID::is_t<Expression::String>(pattern),
                               WHOAMI_WITH_SOURCE "pattern expression must be a String");
            Utils::affirm<Err>(CUID::is_t<Expression::BV>(start_index),
                               WHOAMI_WITH_SOURCE "start_index expression must be a BV");
        }
    };

} // namespace Op::String

#endif
