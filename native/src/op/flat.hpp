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
 *  Optionally pass a template argument to require all of input be the type
 */
#define OP_FLAT_TRIVIAL_SUBCLASS(CLASS, ...)                                                      \
    class CLASS final : public Flat<__VA_ARGS__> {                                                \
        OP_FINAL_INIT(CLASS)                                                                      \
      private:                                                                                    \
        /** Private constructor */                                                                \
        explicit inline CLASS(const Hash::Hash &h, OpContainer &&input)                           \
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
     *	Will verify that each input operand subclasses T
     */
    template <typename T = Expression::Base> class Flat : public FlatBase {
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

            // Verify there are at least 2 operands
            Utils::affirm<Err::Size>(operands.size() >= 2,
                                     "Op::Flat constructor requires at least two arguments");

            // Verify inputs subclass T
            const auto cuid = operands[0]->cuid;
            if constexpr (std::is_final_v<T>) {
                Utils::affirm<Err::Type>(cuid == T::static_cuid,
                                         "Op::Flat operands do not subclass given T");
            }
            else {
                Utils::affirm<Err::Type>(
                    dynamic_cast<const T *>(operands[0].get()) != nullptr,
                    "Op::Flat: Input operand either points to null, or is not a subclass of T");
            }

            // Verify all inputs are the same
            for (const auto &i : operands) {
                Utils::affirm<Err::Type>(
                    i->cuid == cuid,
                    "The cuids of left and right differ for Op::Flat's constructor."
                    " This indicates that left and right are of different types, which"
                    " is not allowed.");
            }
        }
    };

    /** Default virtual destructor */
    template <typename T> Flat<T>::~Flat() noexcept = default;

} // namespace Op

#endif
