/**
 * @file
 * @brief This defines SOC::Symbolic
 */
#ifndef __SOC_SYMBOLIC_HPP__
#define __SOC_SYMBOLIC_HPP__

#include "base.hpp"

#include <string>


// Forward declarations
namespace Utils {
    template <typename, typename> class Cache;
}

namespace SOC {

    /** A symbolic variable */
    struct Symbolic : public Base {

        /** Returns true */
        bool symbolic() const noexcept override final;

        /** Static hash function */
        static Hash::Hash hash(const std::string &s);

        /** The name of the symbol */
        const std::string name;

      private:
        /** Private constructor
         *  Note: const ref is preferrable here as then we don't have to worry about
         *  when name is moved when trying to hash(name) for the Hashed superclass
         */
        Symbolic(const std::string &name);

        /** Allow cache friend access
         *  We expose the constructor so that the cache may emplace new objects, which is
         *  faster than copying them in
         */
        friend class ::Utils::Cache<Hash::Hash, Base>;
    };

} // namespace SOC

#endif
