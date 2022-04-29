/**
 * @file
 * @brief This file defines the String::SubString class
 */
#ifndef R_SRC_OP_STRING_SUBSTRING_HPP_
#define R_SRC_OP_STRING_SUBSTRING_HPP_

#include "../base.hpp"


namespace Op::String {

    /** The op class: String::SubString */
    class SubString final : public Base {
        OP_FINAL_INIT(SubString, "String::");

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

        /** repr */
        inline void repr_stream(std::ostream &out) const final {
            out << R"|({ "name":")|" << op_name() << R"|(", "start_index":)|";
            start_index->repr_stream(out);
            out << R"|(, "count":)|";
            count->repr_stream(out);
            out << R"|(, "full_string":)|";
            full_string->repr_stream(out);
            out << " }";
        }

        /** Appends the expr children of the expr to the given vector
         *  Note: This should only be used when returning children to python
         */
        inline std::vector<ArgVar> python_children() const final {
            return { start_index, count, full_string };
        }

      private:
        /** Private constructor
         *  Ensure that each argument is of the proper type
         */
        explicit inline SubString(const Hash::Hash &h, const Expr::BasePtr &si,
                                  const Expr::BasePtr &c, const Expr::BasePtr &s)
            : Base { h, static_cuid }, start_index { si }, count { c }, full_string { s } {
            using E = Error::Expr::Type;
            UTIL_ASSERT(E, CUID::is_t<Expr::BV>(start_index), "start_index expr must be a BV");
            UTIL_ASSERT(E, CUID::is_t<Expr::BV>(count), "count expr must be a BV");
            UTIL_ASSERT(E, CUID::is_t<Expr::String>(full_string),
                        "full_string expr must be a String");
        }

        /** Adds the raw expr children of the expr to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        inline void unsafe_add_reversed_children(Stack &s) const final {
            s.emplace(full_string.get());
            s.emplace(count.get());
            s.emplace(start_index.get());
        }
    };

} // namespace Op::String

#endif
