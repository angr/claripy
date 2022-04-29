/**
 * @file
 * @brief This file defines the generic Extract Op class
 */
#ifndef R_SRC_OP_EXTRACT_HPP_
#define R_SRC_OP_EXTRACT_HPP_

#include "base.hpp"


namespace Op {

    /** The op class: Extract */
    class Extract final : public Base {
        OP_FINAL_INIT(Extract, "", 0);

      public:
        /** High index */
        const U64 high;
        /** Low index */
        const U64 low;
        /** What we extract from */
        const Expr::BasePtr from;

        /** repr */
        inline void repr_stream(std::ostream &out) const final {
            out << R"|({ "name":")|" << op_name() << R"|(", "high":)|" << high << R"|(, "low":)|"
                << low << R"|(, "from":)|";
            from->repr_stream(out);
            out << " }";
        }

        /** Appends the expr children of the expr to the given vector
         *  Note: This should only be used when returning children to python
         */
        inline std::vector<ArgVar> python_children() const final { return { high, low, from }; }

      private:
        /** Private constructor */
        explicit inline Extract(const Hash::Hash &h, const U64 hi, const U64 lo,
                                const Expr::BasePtr &f)
            : Base { h, static_cuid }, high { hi }, low { lo }, from { f } {}

        /** Adds the raw expr children of the expr to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        inline void unsafe_add_reversed_children(Stack &s) const final { s.emplace(from.get()); }
    };

} // namespace Op

#endif
