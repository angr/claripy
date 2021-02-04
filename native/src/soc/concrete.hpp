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
    struct Concrete final : public Base {
        SOC_INIT
      public:
        /** Returns false */
        inline bool symbolic() const noexcept override final { return false; }

        /** Destructor */
        ~Concrete() noexcept override final = default;

      private:
        /** Private constructor */
        explicit inline Concrete(const Hash::Hash &h) noexcept : Base { h, static_cuid } {}

        // Disable other methods of construction
        SET_IMPLICITS_CONST_MEMBERS(Concrete, delete, noexcept)
    };

} // namespace SOC

#endif
