/**
 * @file
 * @brief This defines SOC::Concrete
 */
#ifndef __SOC_CONCRETE_HPP__
#define __SOC_CONCRETE_HPP__

#include "base.hpp"

#include "../utils.hpp"


// Forward declarations
namespace Utils {
    template <typename, typename> class Cache;
}

namespace SOC {

    /** A concrete variable */
    struct Concrete : public Base {

        /** Returns false */
        constexpr bool symbolic() const noexcept override final { return false; }

        /** Static hash function to satisfy factory */
        static constexpr Hash::Hash hash() { return UTILS_FILE_LINE_HASH; }

      private:
        /** Private constructor */
        inline Concrete() noexcept : Base { hash() } {}

        /** Destructor */
        ~Concrete() noexcept override final = default;

        // Disable other methods of construction
        SET_IMPLICITS_CONST_MEMBERS(Base, delete, noexcept)

        /** Allow cache friend access
         *  We expose the constructor so that the cache may emplace new objects, which is
         *  faster than copying them in
         */
        friend class ::Utils::Cache<Hash::Hash, Base>;
    };

} // namespace SOC

#endif
