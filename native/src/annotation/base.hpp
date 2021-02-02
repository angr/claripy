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


namespace Annotation {

    /** Annotations are used to achieve claripy's goal of being an arithmetic instrumentation
     * engine. They provide a means to pass extra information to the claripy backends.
     */
    struct Base : public Hash::Hashed {

        /** Constructor */
        explicit inline Base(const Hash::Hash &h = default_hash) : Hashed { h } {}

        /** Virtual destructor */
        virtual ~Base();

        // Rule of 5
        SET_IMPLICITS_NONDEFAULT_CTORS(Base, default)
        SET_IMPLICITS_OPERATORS(Base, delete)

        /** Returns whether this annotation can be eliminated in a simplification.
         * True if eliminatable, False otherwise
         */
        virtual inline bool eliminatable() const { return true; }

        /** Returns whether this annotation can be relocated in a simplification.
         *  True if it can be relocated, false otherwise.
         */
        virtual bool relocatable() const { return false; }

        /** The default hash of an Annotation::Base */
        static const constexpr Constants::UInt default_hash { UTILS_FILE_LINE_HASH };
    };

} // namespace Annotation

#endif
