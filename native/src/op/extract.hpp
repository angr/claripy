/**
 * @file
 * @brief This file defines the generic Extract Op class
 */
#ifndef R_OP_EXTRACT_HPP_
#define R_OP_EXTRACT_HPP_

#include "base.hpp"


namespace Op {

    /** The op class: Extract */
    class Extract final : public Base {
        OP_FINAL_INIT(Extract, "", 0);

      public:
        /** High index */
        const UInt high;
        /** Low index */
        const UInt low;
        /** What we extract from */
        const Expr::BasePtr from;

        /** Python's repr function (outputs json) */
        inline void repr(std::ostream &out) const final {
            out << R"|({ "name":")|" << op_name() << R"|(", "high":)|" << high << R"|(, "low":)|"
                << low << R"|(, "from":)|";
            from->repr(out);
            out << " }";
        }

        /** Adds the raw expr children of the expr to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        inline void unsafe_add_reversed_children(Stack &s) const final { s.emplace(from.get()); }

        /** Appends the expr children of the expr to the given vector
         *  Note: This should only be used when returning children to python
         */
        inline void python_children(std::vector<ArgVar> &v) const final {
            v.emplace_back(high);
            v.emplace_back(low);
            v.emplace_back(from);
        }

      private:
        /** Protected constructor */
        explicit inline Extract(const Hash::Hash &h, const UInt hi, const UInt lo,
                                const Expr::BasePtr &f)
            : Base { h, static_cuid }, high { hi }, low { lo }, from { f } {}
    };

} // namespace Op

#endif
