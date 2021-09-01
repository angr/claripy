/**
 * @file
 * @brief This file defines the concrete backend
 */
#ifndef R_BACKEND_CONCRETE_CONCRETE_HPP_
#define R_BACKEND_CONCRETE_CONCRETE_HPP_

#include "constants.hpp"


namespace Backend::Concrete {

    /** The Concrete backend */
    class Concrete final : Super {
        ENABLE_UNITTEST_FRIEND_ACCESS;
        static_assert(!use_apply_annotations, "Concrete objects cannot hold annotations");

      public:
        // Rule of 5
        DEFINE_IMPLICITS_ALL_NOEXCEPT(Concrete);

        /********************************************************************/
        /*                        Function Overrides                        */
        /********************************************************************/

        /** Destructor */
        ~Concrete() noexcept override = default;

        /** Clears translocation data */
        inline void clear_persistent_data() override final {}

        /** The name of this backend */
        [[nodiscard]] inline const char *name() const noexcept override final {
            return "concrete";
        }

        /** Simplify the given expression
         *  expr may not be nullptr
         */
        inline Expression::BasePtr simplify(const Expression::RawPtr expr) override final {
            UTILS_AFFIRM_NOT_NULL_DEBUG(expr);
            return nullptr; // todo
        }

        /** This dynamic dispatcher converts expr into a backend object
         *  All arguments of expr that are not primitives have been
         *  pre-converted into backend objects and are in args
         *  Arguments must be popped off the args stack if used
         *  expr may not be nullptr
         *  Warning: This function may internally do unchecked static casting, we permit this
         *  *only* if the cuid of the expression is of or derive from the type being cast to.
         */
        inline PrimVar dispatch_conversion(const Expression::RawPtr expr,
                                           std::vector<const PrimVar *> &args) override final {
            Utils::sink(expr, args);
            return 0.; // todo
        }

        /** Abstract a backend object into a claricpp expression */
        inline AbstractionVariant
        dispatch_abstraction(const PrimVar &b_obj,
                             std::vector<AbstractionVariant> &args) override final {
            Utils::sink(b_obj, args);
            return Mode::FP::Rounding::NearestTiesAwayFromZero; // todo
        }

        /********************************************************************/
        /*                         Member Functions                         */
        /********************************************************************/


      private:
        /********************************************************************/
        /*                     Private Helper Functions                     */
        /********************************************************************/


        /********************************************************************/
        /*                          Representation                          */
        /********************************************************************/
    };

} // namespace Backend::Concrete

#endif
