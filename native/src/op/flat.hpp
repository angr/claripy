/**
 * @file
 * @brief A 'flat' Op. I.e. An op that takes a vector<Expr::BasePtr> of inputs
 * For example, Add(a,b) can become A({a, b, c, d, ... }) if flattened
 */
#ifndef R_OP_FLAT_HPP_
#define R_OP_FLAT_HPP_

#include "base.hpp"


/** A macro used to define a trivial subclass of Flat
 *  Pass template arguments to Binary via variadic macro arguments
 *  If ConsiderSize, sizes will be compared as well when type checking if applicable
 *  An additional argument can be passed as the prefix to the desired debug name of the class
 *  For example, "FP::" may be desired for an FP op
 *  X can be anything, but must be different between different templates of the same class
 *  For example, Foo<int> must give a different X from Foo<bool>
 */
#define OP_FLAT_TRIVIAL_SUBCLASS(CLASS, CONSIDERSIZE, X, ...)                                      \
    class CLASS final : public ::Op::Flat<(CONSIDERSIZE)> {                                        \
        OP_FINAL_INIT(CLASS, (X), "" __VA_ARGS__);                                                 \
                                                                                                   \
      private:                                                                                     \
        /** Private constructor */                                                                 \
        explicit inline CLASS(const ::Hash::Hash &h, FlatArgs &&input)                             \
            : Flat { h, static_cuid, std::move(input) } {}                                         \
    };


namespace Op {

    /** Operand container type used for flat ops */
    using FlatArgs = std::vector<Expr::BasePtr>;

    /** An abstract flattened Op class
     *  Operands must all be of the same type and there must be at least 2
     *  These conditions are *not* validated
     */
    class AbstractFlat : public Base {
        OP_PURE_INIT(AbstractFlat);

      public:
        /** Operands */
        const FlatArgs operands;

        /** Return true if this class requires each operand be of the same size */
        virtual bool consider_size() const noexcept = 0;

        /** Adds the raw expr children of the expr to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        inline void unsafe_add_reversed_children(Stack &s) const final {
            for (auto i { operands.crbegin() }; i != operands.crend(); ++i) {
                UTIL_ASSERT_NOT_NULL_DEBUG(i->get());
                s.emplace(i->get());
            }
        }

        /** Appends the expr children of the expr to the given vector
         *  Note: This should only be used when returning children to python
         */
        inline void python_children(std::vector<ArgVar> &v) const final {
            v.reserve(v.size() + operands.size());
            for (const auto &i : operands) {
                UTIL_ASSERT_NOT_NULL_DEBUG(i);
                v.emplace_back(i);
            }
        }

      protected:
        /** Protected constructor
         *  Verify that all operands are of the same type and that there are at least 2
         */
        explicit inline AbstractFlat(const Hash::Hash &h, const CUID::CUID &cuid_, FlatArgs &&input)
            : Base { h, cuid_ }, operands { input } {}
    };

    /** Default virtual destructor */
    AbstractFlat::~AbstractFlat() noexcept = default;


    /** A flattened Op class
     *  Operands must all be of the same type and there must be at least 2
     *  Both of these conditions are verified during construction
     *  If ConsiderSize, sizes will be compared as well when type checking if applicable
     */
    template <bool ConsiderSize> class Flat : public AbstractFlat {
        OP_PURE_INIT(Flat);

      public:
        /** Return ConsiderSize */
        inline bool consider_size() const noexcept final { return ConsiderSize; }

        /** Python's repr function (outputs json) */
        inline void repr(std::ostream &out) const final {
            out << R"|({ "name":")|" << op_name() << R"|(", "consider_size":)|" << std::boolalpha
                << ConsiderSize << R"|(, "args":[ )|";
            operands[0]->repr(out);
            for (UInt i = 1; i < operands.size(); ++i) {
                out << ", ";
                operands[i]->repr(out);
            }
            out << " ] }";
        }

      protected:
        /** Protected constructor
         *  Verify that all operands are of the same type and that there are at least 2
         */
        explicit inline Flat(const Hash::Hash &h, const CUID::CUID &cuid_, FlatArgs &&input)
            : AbstractFlat { h, cuid_, std::move(input) } {
            namespace Err = Error::Expr;

            // Operands size
            UTIL_ASSERT(Err::Size, operands.size() >= 2,
                        "constructor requires at least two arguments");

            // Verify all inputs are the same type
            for (const auto &i : operands) {
                const bool same { Expr::are_same_type<ConsiderSize>(operands[0], i) };
                UTIL_ASSERT(Err::Type, same, "operands differ by type",
                            ConsiderSize ? " or size" : "");
            }
        }
    };

    /** Default virtual destructor */
    template <bool B> Flat<B>::~Flat() noexcept = default;


    /** Returns true if T is flat */
    template <typename T>
    UTIL_ICCBOOL is_flat { Util::Type::Is::ancestor<Flat<true>, T> ||
                           Util::Type::Is::ancestor<Flat<false>, T> };

} // namespace Op

#endif
