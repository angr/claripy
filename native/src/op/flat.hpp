/**
 * @file
 * @brief A 'flat' Op. I.e. An op that takes a vector<T> of inputs
 * For example, Add(a,b) can become A({a, b, c, d, ... }) if flattened
 */
#ifndef __OP_FLAT_HPP__
#define __OP_FLAT_HPP__

#include "base.hpp"

#include <memory>


// Forward declarations
namespace Expression {
    class Bool;
} // namespace Expression

namespace Op {

    /** A flattened Op class */
    template <typename T = Expression::Base> class Flat : public Base {
        OP_PURE_INIT(Flat)
      public:
        /** Operand container type */
        using OpContainer = std::vector<Factory::Ptr<T>>;

        /** Operands */
        const OpContainer operands;

      protected:
        /** Protected constructor */
        explicit inline Flat(const Hash::Hash &h, const CUID::CUID &cuid_, OpContainer &&input)
            : Base { h, cuid_ }, operands { input } {}
    };

    /** Default virtual destructor */
    template <typename T> Flat<T>::~Flat() noexcept = default;

} // namespace Op

#endif
