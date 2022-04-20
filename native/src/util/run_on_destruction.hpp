/**
 * @file
 * \ingroup util
 * @brief This file defines Util::RunOnDestruction
 */
#ifndef R_SRC_UTIL_RUNONDESTRUCTION_HPP_
#define R_SRC_UTIL_RUNONDESTRUCTION_HPP_

#include "../macros.hpp"

#include <exception>
#include <functional>


namespace Util {

    /** Runs f() when this is destructed unless disabled
     *  f() must have the type signature: void()
     *  Note: We use the template to permit passing callable objects as well
     *  As such, F can be the return of a lambda, or a callable object, for example
     *  If NoExcept is set to false, the destructor may throw; by default it is true
     */
    template <typename F, bool NoExcept = true> class [[nodiscard]] RunOnDestruction final {
      public:
        /** Constructor */
        explicit RunOnDestruction(const F &func) : f(func) {}

        /** Move Constructor */
        explicit RunOnDestruction(RunOnDestruction &&old) noexcept
            : enabled(old.enabled), f(std::move(old.f)) {
            old.f = nullptr;
            old.disable();
        }

        /** Destructor */
        ~RunOnDestruction() noexcept(NoExcept) {
            if (enabled) {
                if constexpr (NoExcept) {
                    try {
                        f();
                    }
                    // Prevent the program from crashing
                    catch (std::exception &) {
                    }
                }
                else {
                    f();
                }
            }
        }

        /** Move Assignment Operator */
        RunOnDestruction &operator=(RunOnDestruction &&old) noexcept {
            if (this != &old) {
                old.enabled() ? enable() : disable();
                old.disable();
                f = old.f;
                old.f = nullptr;
            }
            return *this;
        }

        /** Return true iff enabled */
        bool status() const noexcept { return enabled; }

        /** Enable f on destruction */
        void enable() noexcept { enabled = true; }

        /** Disable f on destruction */
        void disable() noexcept { enabled = false; }

      private:
        /** Disable copy construction */
        RunOnDestruction(const RunOnDestruction &) = delete;
        /** Disable copy assignment */
        RunOnDestruction &operator=(const RunOnDestruction &) = delete;

        /** Determine if f should be run on destruction or not
         *  Default: enabled
         */
        bool enabled { true };

        /** The function to be invoked on destruction */
        std::function<void()> f;
    };

} // namespace Util

#endif
