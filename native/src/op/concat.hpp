/**
 * @file
 * @brief The OP representing the == comparison
 */
#ifndef __OP_CONCAT_HPP__
#define __OP_CONCAT_HPP__

#include "binary.hpp"

#include <memory>


// Forward declarations
namespace Expression {
    class Bits;
} // namespace Expression

namespace Op {

    /** The comparison op class: Eq */
    class Concat final : public Binary<Expression::Bits> {
        OP_FINAL_INIT(Eq)
      private:
        /** Private constructor */
        explicit inline Eq(const Hash::Hash &h, const Factory::Ptr<Expression::Base> &l,
                           const Factory::Ptr<Expression::Base> &r)
            : Binary { h, static_cuid, l, r } {}
    };

} // namespace Op

#endif
