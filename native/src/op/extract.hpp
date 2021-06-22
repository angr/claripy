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
        OP_FINAL_INIT(Extract, 0);

      public:
        /** High index */
        const Constants::UInt high;
        /** Low index */
        const Constants::UInt low;
        /** What we extract from */
        const Expression::BasePtr from;

        /** Python's repr function (outputs json) */
        inline void repr(std::ostream &out, const bool verbose = false) const override final {
            out << R"|({ "name":")|" << op_name() << R"|(", "high":)|" << high << R"|(, "low":)|"
                << low << R"|(, "from":)|";
            Expression::repr(from, out, verbose);
            out << " }";
        }

        /** Add's the raw expression children of the expression to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        inline void add_reversed_children(Stack &s) const override final { s.emplace(from.get()); }

      private:
        /** Protected constructor */
        explicit inline Extract(const Hash::Hash &h, const Constants::UInt hi,
                                const Constants::UInt lo, const Expression::BasePtr &f)
            : Base { h, static_cuid }, high { hi }, low { lo }, from { f } {}
    };

} // namespace Op

#endif
