/**
 * @file
 * @brief A 'flat' Op. I.e. An op that takes a vector<T> of inputs
 * For example, Add(a,b) can become A({a, b, c, d, ... }) if flattened
 */
#ifndef __OP_FLAT_HPP__
#define __OP_FLAT_HPP__

#include "base.hpp"

#include <memory>


/** A macro used to define a trivial subclass of Flat
 *  Optionally private a type that Flat templates on
 */
#define OP_FLAT_TRIVIAL_SUBCLASS(CLASS, ...)                                                      \
    class CLASS final : public Flat<__VA_ARGS__> {                                                \
        OP_FINAL_INIT(CLASS)                                                                      \
      private:                                                                                    \
        /** Private constructor */                                                                \
        explicit inline CLASS(const Hash::Hash &h, OpContainer &&input)                           \
            : Flat { h, static_cuid, std::forward<OpContainer>(input) } {}                        \
    };


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
