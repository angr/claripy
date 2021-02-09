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
}

namespace Op {

    /** The comparison op class: Eq */
    class Concat final : public Binary<Expression::Bits> {
        OP_FINAL_INIT(Concat)
      private:
        /** Private constructor */
        explicit inline Concat(const Hash::Hash &h, const Operand &l, const Operand &r)
            : Binary { h, static_cuid, l, r } {}
    };

} // namespace Op

#endif
