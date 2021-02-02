/**
 * @file
 * @brief This defines SOC::Concrete
 */
#ifndef __SOC_CONCRETE_HPP__
#define __SOC_CONCRETE_HPP__

#include "base.hpp"


// Forward declarations
namespace Utils {
    template <typename, typename> class Cache;
}

namespace SOC {

    /** A concrete variable */
    struct Concrete : public Base {

        /** Returns false */
        bool symbolic() const noexcept override final;

        /** Static hash function to satisfy factory */
        static Hash::Hash hash();

      private:
        /** Private constructor */
        Concrete();

        /** Allow cache friend access
         *  We expose the constructor so that the cache may emplace new objects, which is
         *  faster than copying them in
         */
        friend class ::Utils::Cache<Hash::Hash, Base>;
    };

} // namespace SOC

#endif
