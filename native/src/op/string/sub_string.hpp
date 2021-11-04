/**
 * @file
 * @brief This file defines the String::SubString class
 */
#ifndef R_OP_STRING_SUBSTRING_HPP_
#define R_OP_STRING_SUBSTRING_HPP_

#include "../base.hpp"


namespace Op::String {

    /** The op class: String::SubString */
    class SubString final : public Base {
        OP_FINAL_INIT(SubString, 0, "String::");

      public:
        /** The start index of the substring stored as a BV
         *  Note: We leave it as a base for optimizations purposes
         */
        const Expr::BasePtr start_index;
        /** The count of the substring stored as a BV
         *  Note: We leave it as a base for optimizations purposes
         */
        const Expr::BasePtr count;
        /** The count of the substring stored as a String
         *  Note: We leave it as a base for optimizations purposes
         */
        const Expr::BasePtr full_string;

        /** Python's repr function (outputs json) */
        inline void repr(std::ostream &out, const bool verbose = false) const override final {
            out << R"|({ "name":")|" << op_name() << R"|(", "start_index":)|";
            Expr::repr(start_index, out, verbose);
            out << R"|(, "count":)|";
            Expr::repr(count, out, verbose);
            out << R"|(, "full_string":)|";
            Expr::repr(full_string, out, verbose);
            out << " }";
        }

        /** Adds the raw expr children of the expr to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        inline void unsafe_add_reversed_children(Stack &s) const override final {
            s.emplace(full_string.get());
            s.emplace(count.get());
            s.emplace(start_index.get());
        }

      private:
        /** Protected constructor
         *  Ensure that each argument is of the proper type
         */
        explicit inline SubString(const Hash::Hash &h, const Expr::BasePtr &si,
                                  const Expr::BasePtr &c, const Expr::BasePtr &s)
            : Base { h, static_cuid }, start_index { si }, count { c }, full_string { s } {
            using E = Error::Expr::Type;
            Util::affirm<E>(CUID::is_t<Expr::BV>(start_index),
                            WHOAMI "start_index expr must be a BV");
            Util::affirm<E>(CUID::is_t<Expr::BV>(count), WHOAMI "count expr must be a BV");
            Util::affirm<E>(CUID::is_t<Expr::String>(full_string),
                            WHOAMI "full_string expr must be a String");
        }
    };

} // namespace Op::String

#endif
