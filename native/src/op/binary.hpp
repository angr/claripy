/**
 * @file
 * @brief A binary Op; takes two inputs of the same type
 * For example: Concat(Str1, Str2)
 */
#ifndef __OP_BINARY_HPP__
#define __OP_BINARY_HPP__

#include "base.hpp"

#include "../error.hpp"

#include <memory>


/** A macro used to define a trivial subclass of Binary
 *  Optionally pass a template argument to require all of input be the type
 */
#define OP_BINARY_TRIVIAL_SUBCLASS(CLASS, ...)                                                    \
    class CLASS final : public Binary<__VA_ARGS__> {                                              \
        OP_FINAL_INIT(CLASS)                                                                      \
      private:                                                                                    \
        /** Private constructor */                                                                \
        explicit inline CLASS(const Hash::Hash &h, const Expression::BasePtr &l,                  \
                              const Expression::BasePtr &r)                                       \
            : Binary { h, static_cuid, l, r } {}                                                  \
    };


namespace Op {

    /** A binary Base op class
     *  All templated binary classes must subclass this
     *  To check if a class is binary, check if it subclasses BinaryBase
     */
    struct BinaryBase : public Base {
        /** Use parent constructors */
        using Base::Base;
        OP_PURE_INIT(BinaryBase)
    };
    /** Default destructor */
    BinaryBase::~BinaryBase() noexcept = default;

    /** A Binary Op class
     *  Operands must all be of the same type
     *	Will verify that each input operand subclasses T
     */
    template <typename T = Expression::Base> class Binary : public BinaryBase {
        OP_PURE_INIT(Binary)
      public:
        /** Left operand */
        const Expression::BasePtr left;

        /** Right operand */
        const Expression::BasePtr right;

      protected:
        /** Protected constructor */
        explicit inline Binary(const Hash::Hash &h, const CUID::CUID &cuid_,
                               const Expression::BasePtr &l, const Expression::BasePtr &r)
            : BinaryBase { h, cuid_ }, left { l }, right { r } {
            using Err = Error::Expression::Type;

            // Error checking
            Utils::affirm<Err>(left->cuid == right->cuid,
                               "The cuids of left and right differ for Op::Binary's constructor."
                               " This indicates that left and right are of different types, which"
                               " is not allowed.");

            // Verify inputs subclass T
            if constexpr (std::is_final_v<T>) {
                Utils::affirm<Err>(left->cuid == T::static_cuid,
                                   "Op::Flat operands do not subclass given T");
            }
            else {
                Utils::affirm<Err>(
                    dynamic_cast<const T *>(left.get()) != nullptr,
                    "Op::Flat: Input operand either points to null, or is not a subclass of T");
            }
        }
    };

    /** Default virtual destructor */
    template <typename T> Binary<T>::~Binary() noexcept = default;

} // namespace Op

#endif
