/**
 * @file
 * @brief This file defines the String::SubString class
 */
#ifndef __OP_STRING_SUBSTRING_HPP__
#define __OP_STRING_SUBSTRING_HPP__

#include "../base.hpp"


namespace Op::String {

    /** The op class: String::SubString */
    class SubString final : public Base {
        OP_FINAL_INIT(SubString)
      public:
        /** The start index of the substring stored as a BV
         *  Note: We leave it as a base for optimizations purposes
         */
        const Expression::BasePtr start_index;
        /** The count of the substring stored as a BV
         *  Note: We leave it as a base for optimizations purposes
         */
        const Expression::BasePtr count;
        /** The count of the substring stored as a String
         *  Note: We leave it as a base for optimizations purposes
         */
        const Expression::BasePtr full_string;

      private:
        /** Protected constructor
         *  Ensure that each argument is of the proper type
         */
        explicit inline SubString(const Hash::Hash &h, const Expression::BasePtr &si,
                                  const Expression::BasePtr &c, const Expression::BasePtr &s)
            : Base { h, static_cuid }, start_index { si }, count { c }, full_string { s } {
            using Err = Error::Expression::Type;
            Utils::affirm<Err>(CUID::is_t<Expression::BV>(start_index),
                               WHOAMI_WITH_SOURCE "start_index expression must be a BV");
            Utils::affirm<Err>(CUID::is_t<Expression::BV>(count),
                               WHOAMI_WITH_SOURCE "count expression must be a BV");
            Utils::affirm<Err>(CUID::is_t<Expression::String>(full_string),
                               WHOAMI_WITH_SOURCE "full_string expression must be a String");
        }
    };

} // namespace Op::String

#endif
