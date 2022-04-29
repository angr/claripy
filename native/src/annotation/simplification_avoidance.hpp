/**
 * @file
 * @brief This file defines the Annotation::SimplificationAvoidance class
 */
#ifndef R_SRC_ANNOTATION_SIMPLIFICATIONAVOIDANCE_HPP_
#define R_SRC_ANNOTATION_SIMPLIFICATIONAVOIDANCE_HPP_

#include "base.hpp"


namespace Annotation {

    /** A built-in annotation */
    class SimplificationAvoidance final : public Base {
        FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(Base)
      public:
        /** Constructor */
        explicit inline SimplificationAvoidance(const Hash::Hash &h) noexcept
            : Base { h, static_cuid } {}

        /** Get the Expr's repr */
        virtual inline void repr_stream(std::ostream &out) const final {
            out << R"({"Annotation Type":"SimplificationAvoidance"})";
        }

        /** Returns whether this annotation can be eliminated in a simplification. */
        inline bool eliminatable() const final { return false; }

        /** Returns whether this annotation can be relocated in a simplification. */
        inline bool relocatable() const final { return false; }

        /** name */
        virtual inline const char *name() const final { return "SimplificationAvoidance"; }
    };

} // namespace Annotation

#endif
