/**
 * @file
 * @brief A binary Op; one that takes two inputs of the same type
 * For example: Concat(Str1, Str2)
 */
#ifndef __OP_BINARY_HPP__
#define __OP_BINARY_HPP__

#include "base.hpp"

#include <memory>


/** A macro used to define a trivial subclass of Binary
 *  Optionally private a type that Binary templates on
 */
#define OP_BINARY_TRIVIAL_SUBCLASS(CLASS, ...)                                                    \
    class CLASS final : public Binary<__VA_ARGS__> {                                              \
        OP_FINAL_INIT(CLASS)                                                                      \
      private:                                                                                    \
        /** Private constructor */                                                                \
        explicit inline CLASS(const Hash::Hash &h, const Operand &l, const Operand &r)            \
            : Binary { h, static_cuid, l, r } {}                                                  \
    };


namespace Op {

    /** A flattened Op class
     *  T must derive from Expression::Base but we do not enforce this
     *  to avoid cyclic header inclusion issues
     */
    template <typename T = Expression::Base> class Binary : public Base {
        OP_PURE_INIT(Binary)
      public:
        /** The operand type */
        using Operand = Factory::Ptr<T>;

        /** Left operand */
        const Operand left;
        /** Right operand */
        const Operand right;

      protected:
        /** Protected constructor */
        explicit inline Binary(const Hash::Hash &h, const CUID::CUID &cuid_, const Operand &l,
                               const Operand &r)
            : Base { h, cuid_ }, left { l }, right { r } {}
    };

    /** Default virtual destructor */
    template <typename T> Binary<T>::~Binary() noexcept = default;

} // namespace Op

#endif
