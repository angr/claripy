/**
 * @file
 * @brief This file defines the Annotation::Base class
 */
#ifndef __ANNOTATION_BASE_HPP__
#define __ANNOTATION_BASE_HPP__

#include "../constants.hpp"
#include "../hash.hpp"
#include "../macros.hpp"

#include <memory>
#include <utility>


// Forward declarations
namespace Expression {
    namespace Raw {
        class Base;
    }
    using Base = std::shared_ptr<Raw::Base>;
} // namespace Expression

namespace Annotation {

    /** Annotations are used to achieve claripy's goal of being an arithmetic instrumentation
     * engine. They provide a means to pass extra information to the claripy backends.
     */
    struct Base : public Hash::Hashed {

        /** Constructor */
        Base(const Hash::Hash &h = default_hash);

        /** Virtual destructor */
        virtual ~Base();

        // Rule of 5
        SET_IMPLICITS_NONDEFAULT_CTORS(Base, default)
        SET_IMPLICITS_OPERATORS(Base, delete)

        /** Returns whether this annotation can be eliminated in a simplification.
         * True if eliminatable, False otherwise
         */
        virtual bool eliminatable() const;

        /** Returns whether this annotation can be relocated in a simplification.
         *  True if it can be relocated, false otherwise.
         */
        virtual bool relocatable() const;

        /** This is called when an annotation has to be relocated because of simplifications.
         *  Consider the following case:
         *      x = claripy.BVS('x', 32)
         *      zero = claripy.BVV(0, 32).add_annotation(your_annotation)
         *      y = x + zero
         *  Here, one of three things can happen:
         *      1. if your_annotation.eliminatable is True, the simplifiers will simply
         *         eliminate your_annotation along with `zero` and `y is x` will hold
         *      2. elif your_annotation.relocatable is False, the simplifier will abort
         *         and y will never be simplified
         *      3. elif your_annotation.relocatable is True, the simplifier will run,
         *         determine that the simplified result of `x + zero` will be `x`. It
         *         will then call your_annotation.relocate(zero, x) to move the annotation
         *         away from the Expression that is about to be eliminated.
         *  src: the old Expression that was eliminated in the simplification
         *  dst: the new Expression (the result of a simplification)
         *  return: a pointer to the annotation that will be applied to `dst`
         */
        virtual const Base *relocate(const Expression::Base &src,
                                     const Expression::Base &dst) const;

        /** The default hash of an Annotation::Base */
        static const constexpr Constants::UInt default_hash { UTILS_FILE_LINE_HASH };
    };

} // namespace Annotation

#endif
