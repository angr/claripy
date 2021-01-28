/**
 * @file
 * \ingroup utils
 * @brief This file defines Utils::RunOnDestruction
 */
#ifndef __UTILS_RUNONDESTRUCTION_HPP__
#define __UTILS_RUNONDESTRUCTION_HPP__

#include "../macros.hpp"

#include <functional>


namespace Utils {

    /** Runs f() when this is destructed unless disabled
     *  f() must have the type signature: void()
     *  Note: We use the template to permit passing callable objects as well
     *  As such, F can be the return of a lambda, or a callable object, for example
     */
    template <typename F> class [[nodiscard]] RunOnDestruction {
      public:
        /** Constructor */
        explicit RunOnDestruction(const F &func) : f(func) {}

        /** Destructor */
        ~RunOnDestruction() {
            if (this->enabled) {
                f();
            }
        }

        /** Enable f on destruction */
        void enable() noexcept { this->enabled = true; }

        /** Disable f on destruction */
        void disable() noexcept { this->enabled = false; }

      private:
        // Disable all other methods of construction
        SET_IMPLICITS(RunOnDestruction, delete)

        /** Determine if f should be run on destruction or not
         *  Default: enabled
         */
        bool enabled { true };

        /** The function to be invoked on destruction */
        const std::function<void()> f;
    };

} // namespace Utils

#endif
