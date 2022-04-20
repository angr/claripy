/**
 * @file
 * @brief This file defines the Annotation::Base class
 */
#ifndef R_SRC_ANNOTATION_BASE_HPP_
#define R_SRC_ANNOTATION_BASE_HPP_

#include "../factory.hpp"
#include "../has_repr.hpp"

#include <memory>
#include <sstream>
#include <utility>


namespace Annotation {

    /** Annotations are used to achieve claripy's goal of being an arithmetic instrumentation
     * engine. They provide a means to pass extra information to the claripy backends.
     */
    struct Base : public HasRepr, public Factory::FactoryMade {
        FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(Base, 0)
      public:
        /** Constructor
         *  CUID must be passed if this is called by a subclass
         */
        explicit inline Base(const Hash::Hash &h, const U64 c = static_cuid) noexcept
            : FactoryMade { h, c } {}

        /** Virtual destructor */
        ~Base() noexcept override = default;

        // Rule of 5
        DEFINE_IMPLICITS_NONDEFAULT_CTORS_ALL_NOEXCEPT(Base);

        /** Get the annotation's repr */
        virtual inline void repr_stream(std::ostream &out) const override {
            out << R"({"Annotation Type":"Base"})";
        }

        /** Returns whether this annotation can be eliminated in a simplification.
         * True if eliminatable, False otherwise
         */
        virtual inline bool eliminatable() const { return true; }

        /** Returns whether this annotation can be relocated in a simplification.
         *  True if it can be relocated, false otherwise.
         */
        virtual inline bool relocatable() const { return false; }

        /** Name */
        virtual inline const char *name() const { return "Base"; }

        /** The default hash of an Annotation::Base */
        static const constexpr U64 default_hash { UTIL_FILE_LINE_HASH };
    };

    /** An alias for Factory::Ptr<Annotation::Base> */
    using BasePtr = Factory::Ptr<const Base>;

} // namespace Annotation

#endif
