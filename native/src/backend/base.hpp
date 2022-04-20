/**
 * @file
 * @brief This file defines the base expr
 */
#ifndef R_SRC_BACKEND_BASE_HPP_
#define R_SRC_BACKEND_BASE_HPP_

#include "../expr.hpp"

#include <memory>
#include <vector>


namespace Backend {

    /** The base Backend type
     *  All backends must subclass this
     */
    class Base {
      public:
        // Define implicits
        DEFINE_IMPLICITS_ALL_NOEXCEPT(Base);

        /** Backend name */
        [[nodiscard]] virtual const char *name() const noexcept = 0;

        /** Check whether the backend can handle the given expr
         *  expr may not be nullptr
         */
        virtual bool handles(const Expr::RawPtr expr) = 0;

        /** Simplify the given expr
         *  expr may not be nullptr
         */
        virtual Expr::BasePtr simplify(const Expr::RawPtr expr) = 0;

        /** Clear caches to decrease memory pressure
         *  Note: if overriding this, it is advised to call this function from the derived version
         */
        virtual inline void downsize() = 0;

        /** Clear persistent data caches
         *  These are caches that are not just for optimization.
         *  It is up to the user to ensure that this function is only called when safe to do so
         *  Warning: Do not use this function unless you understand what it does to the specific
         *  backend that has implemented it! It may clear vital persistent data from memory.
         */
        virtual void clear_persistent_data() = 0;

      protected:
        /** Default destructor */
        virtual ~Base() noexcept = default;
    };

} // namespace Backend

#endif
