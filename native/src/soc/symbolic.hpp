/**
 * @file
 * @brief This defines SOC::Symbolic
 */
#ifndef __SOC_SYMBOLIC_HPP__
#define __SOC_SYMBOLIC_HPP__

#include "base.hpp"

#include "../utils.hpp"

#include <string>


// Forward declarations
namespace Utils {
    template <typename, typename> class Cache;
}

namespace SOC {

    /** A symbolic variable */
    struct Symbolic : public Base {
        CUID_DEFINE_STATIC_CUID

        /** Returns true */
        constexpr bool symbolic() const noexcept override final { return true; }

        /** The name of the symbol */
        const std::string name;

      private:
        /** Private constructor
         *  Note: String copy can throw, but if it does we are out of memory and should crash
         */
        explicit inline Symbolic(const Hash::Hash &h, std::string &&n) noexcept
            : Base { h }, name { n } {}

        /** Destructor */
        ~Symbolic() noexcept override final = default;

        // Disable other methods of construction
        // Technically std::string can throw, but if we are out of memory that is an ok time to
        // crash
        SET_IMPLICITS_CONST_MEMBERS(Base, delete, noexcept)

        /** Allow cache friend access
         *  We expose the constructor so that the cache may emplace new objects, which is
         *  faster than copying them in
         */
        friend class ::Utils::Cache<Hash::Hash, Base>;
    };

} // namespace SOC

#endif
