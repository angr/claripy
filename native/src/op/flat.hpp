/**
 * @file
 * @brief A 'flat' Op. I.e. An op that takes a vector<Expression::BasePtr> of inputs
 * For example, Add(a,b) can become A({a, b, c, d, ... }) if flattened
 */
#ifndef __OP_FLAT_HPP__
#define __OP_FLAT_HPP__

#include "base.hpp"


/** A macro used to define a trivial subclass of Flat
 *  Pass template arguments to Binary via variadic macro arguments
 *  If ConsiderSize, sizes will be compared as well when type checking if applicable
 */
#define OP_FLAT_TRIVIAL_SUBCLASS(CLASS, CONSIDERSIZE)                                             \
    class CLASS final : public ::Op::Flat<CONSIDERSIZE> {                                         \
        OP_FINAL_INIT(CLASS)                                                                      \
      private:                                                                                    \
        /** Private constructor */                                                                \
        explicit inline CLASS(const ::Hash::Hash &h, OpContainer &&input)                         \
            : Flat { h, static_cuid, std::forward<OpContainer>(input) } {}                        \
    };


namespace Op {

    /** A flattened Op class
     *  Operands must all be of the same type and there must be at least 2
     *  Both of these conditions are verified during construction
     *  If ConsiderSize, sizes will be compared as well when type checking if applicable
     */
    template <bool ConsiderSize> class Flat : public Base {
        OP_PURE_INIT(Flat)
      public:
        /** Operand container type */
        using OpContainer = std::vector<Expression::BasePtr>;

        /** Operands */
        const OpContainer operands;

      protected:
        /** Protected constructor
         *  Verify that all operands are of the same type and that there are at least 2
         */
        explicit inline Flat(const Hash::Hash &h, const CUID::CUID &cuid_, OpContainer &&input)
            : Base { h, cuid_ }, operands { input } {
            namespace Err = Error::Expression;

            // Operands size
            Utils::affirm<Err::Size>(operands.size() >= 2, WHOAMI_WITH_SOURCE
                                     "constructor requires at least two arguments");

            // Verify all inputs are the same type
            for (const auto &i : operands) {
                if constexpr (ConsiderSize) {
                    Utils::affirm<Err::Type>(Expression::are_same_type<true>(operands[0], i),
                                             WHOAMI_WITH_SOURCE "operands differ by size or type");
                }
                else {
                    Utils::affirm<Err::Type>(Expression::are_same_type<false>(operands[0], i),
                                             WHOAMI_WITH_SOURCE "operands differ by size");
                }
            }
        }
    };

    /** Default virtual destructor */
    template <bool B> Flat<B>::~Flat() noexcept = default;

    /** Returns true if T is flat */
    template <typename T>
    UTILS_ICCBOOL is_flat { Utils::is_ancestor<Flat<true>, T> ||
                            Utils::is_ancestor<Flat<false>, T> };

} // namespace Op

#endif
