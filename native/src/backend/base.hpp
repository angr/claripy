/**
 * @file
 * @brief This file defines the base expression
 */
#ifndef __BACKEND_BASE_HPP__
#define __BACKEND_BASE_HPP__

#include "../expression.hpp"

#include <memory>
#include <vector>


namespace Backend {

    /** A Solver type */
    using Solver = std::shared_ptr<void>;

    /** The base Backend type
     *  All backends must subclass this
     */
    class Base {
      public:
        // Define implicits
        SET_IMPLICITS(Base, default)

        // Pure virtual functions

        /** Simplify the given expression */
        virtual Expression::BasePtr simplify(const Expression::RawPtr expr) = 0;

        /** Backend name */
        [[nodiscard]] virtual Constants::CCS name() const noexcept = 0;

        /** Check whether the backend can handle the given expression */
        virtual bool handles(const Expression::RawPtr expr) = 0;

        /** Clear caches to decrease memory pressure
         *  Note: if overriding this, it is advised to call this function from the derived version
         */
        virtual inline void downsize() = 0;

      protected:
        /** Default destructor */
        virtual ~Base() = default;
    };

} // namespace Backend

#endif
