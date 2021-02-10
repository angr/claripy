/**
 * @file
 * @brief This file defines the Annotation::Base class
 */
#ifndef __ANNOTATION_BASE_HPP__
#define __ANNOTATION_BASE_HPP__

#include "../factory.hpp"

#include <memory>
#include <utility>


namespace Annotation {

    /** Annotations are used to achieve claripy's goal of being an arithmetic instrumentation
     * engine. They provide a means to pass extra information to the claripy backends.
     */
    struct Base : public Factory::FactoryMade {
        FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(Base)
      public:
        /** Constructor */
        explicit inline Base(const Hash::Hash &h, const Constants::UInt c = static_cuid)
            : FactoryMade { h, c } {}

        /** Virtual destructor */
        virtual ~Base() = default;

        // Rule of 5
        SET_IMPLICITS_NONDEFAULT_CTORS(Base, default, noexcept)

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

    /** An alias for Factory::Ptr<Annotation::Base> */
    using BasePtr = Factory::Ptr<Base>;

} // namespace Annotation

#endif
