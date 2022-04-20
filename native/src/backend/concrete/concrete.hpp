/**
 * @file
 * @brief This file defines the concrete backend
 */
#ifndef R_SRC_BACKEND_CONCRETE_CONCRETE_HPP_
#define R_SRC_BACKEND_CONCRETE_CONCRETE_HPP_

#include "constants.hpp"


namespace Backend::Concrete {

    /** The Concrete backend */
    class Concrete final : Generic<Concrete> {
        ENABLE_UNITTEST_FRIEND_ACCESS;
        /** The backend object type */
        using BackendObj = PrimVar;
        /** Concrete objects cannot hold annotations */
        using ApplyAnnotations = std::false_type;

      public:
        /** Constructor */
        inline Concrete(const Mode::BigInt m = Mode::BigInt::Int) noexcept : Generic { m } {}
        // Disable implicits
        SET_IMPLICITS_NONDEFAULT_CTORS(Concrete, delete);

        /********************************************************************/
        /*                        Function Overrides                        */
        /********************************************************************/

        /** Destructor */
        ~Concrete() noexcept override = default;

        /** Clears translocation data */
        inline void clear_persistent_data() final {}

        /** The name of this backend */
        [[nodiscard]] inline const char *name() const noexcept final { return "concrete"; }

        /** Simplify the given expr
         *  expr may not be nullptr
         */
        inline Expr::BasePtr simplify(const Expr::RawPtr expr) final {
            UTIL_ASSERT_NOT_NULL_DEBUG(expr);
            (void) expr;
            return nullptr; // todo
        }

        /** This dynamic dispatcher converts expr into a backend object
         *  All arguments of expr that are not primitives have been
         *  pre-converted into backend objects and are in args
         *  Arguments must be popped off the args stack if used
         *  expr may not be nullptr
         *  Warning: This function may internally do unchecked static casting, we permit this
         *  *only* if the cuid of the expr is of or derive from the type being cast to.
         */
        inline PrimVar dispatch_conversion(const Expr::RawPtr expr,
                                           std::vector<const PrimVar *> &args, Super &bk) final {
            Util::sink(expr, args, bk);
            return 0.; // todo
        }

        /** Abstract a backend object into a claricpp expr */
        inline AbstractionVariant dispatch_abstraction(const PrimVar &b_obj,
                                                       std::vector<AbstractionVariant> &args,
                                                       Super &bk) final {
            Util::sink(bk, b_obj, args, bk);
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
