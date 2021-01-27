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

    /** Runs f(args...) when this is destructed unless disabled */
    template <typename F, typename... Args> class RunOnDestruction {
      public:
        /** Constructor
         *  Consumes args via move semantics
         *  enabled defaults to true
         */
        RunOnDestruction(const F &func, Args &&...args)
            : enabled(true), f(std::bind(func, std::forward<Args>(args)...)) {}

        /** Destructor */
        ~RunOnDestruction() {
            if (this->enabled) {
                f();
            }
        }

        /** Enable f on destruction */
        void enable() { this->enabled = true; }

        /** Disable f on destruction */
        void disable() { this->enabled = false; }

      private:
        // Disable all other methods of construction
        SET_IMPLICITS(RunOnDestruction, delete)

        /** Determine if f should be run on destruction or not */
        bool enabled;

        /** The function to be invoked on destruction */
        const std::function<void()> f;
    };

} // namespace Utils

#endif
