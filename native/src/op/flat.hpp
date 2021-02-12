/**
 * @file
 * @brief A 'flat' Op. I.e. An op that takes a vector<Expression::BasePtr> of inputs
 * For example, Add(a,b) can become A({a, b, c, d, ... }) if flattened
 */
#ifndef __OP_FLAT_HPP__
#define __OP_FLAT_HPP__

#include "base.hpp"

#include <memory>


/** A macro used to define a trivial subclass of Flat
 *  Pass template arguments to Binary via variadic macro arguments
 */
#define OP_FLAT_TRIVIAL_SUBCLASS(CLASS, ...)                                                      \
    class CLASS final : public ::Op::Flat<__VA_ARGS__> {                                          \
        OP_FINAL_INIT(CLASS)                                                                      \
      private:                                                                                    \
        /** Private constructor */                                                                \
        explicit inline CLASS(const ::Hash::Hash &h, OpContainer &&input)                         \
            : Flat { h, static_cuid, std::forward<OpContainer>(input) } {}                        \
    };


namespace Op {

    /** A flattened Base op class
     *  All templated flat classes must subclass this
     *  To check if a class is flat, check if it subclasses FlatBase
     */
    struct FlatBase : public Base {
        /** Use parent constructors */
        using Base::Base;
        OP_PURE_INIT(FlatBase)
    };
    /** Default destructor */
    FlatBase::~FlatBase() noexcept = default;

    /** A flattened Op class
     *  Operands must all be of the same type and there must be at least 2
     *  Both of these conditions are verified during construction
     *  If ConsiderSize, sizes will be compared as well when type checking if applicable
     *	Will verify that each input operand subclasses T
     */
    template <bool ConsiderSize, typename T = Expression::Base> class Flat : public FlatBase {
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
            : FlatBase { h, cuid_ }, operands { input } {
            namespace Err = Error::Expression;

            // Verify T
            static_assert(Utils::is_ancestor<Expression::Base, T>,
                          "T must derive from Expression::Base");

            // Leftmost operand
            Utils::affirm<Err::Size>(operands.size() >= 2,
                                     "Op::Flat constructor requires at least two arguments");
            Utils::affirm<Err::Type>(Expression::is_t<T, true>(operands[0]),
                                     "Op::Flat leftmost does not subclass given T");

            // Verify all inputs are the same type
            for (const auto &i : operands) {
                if constexpr (ConsiderSize) {
                    Utils::affirm<Err::Type>(Expression::are_same<true>(operands[0], i),
                                             "Op::Flat operands differ by size or type");
                }
                else {
                    Utils::affirm<Err::Type>(Expression::are_same<false>(operands[0], i),
                                             "Op::Flat operands differ by size");
                }
            }
        }
    };

    /** Default virtual destructor */
    template <bool B, typename T> Flat<B, T>::~Flat() noexcept = default;

} // namespace Op

#endif
