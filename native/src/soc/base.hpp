/**
 * @file
 * @brief This defines SOC::Base
 */
#ifndef __SOC_BASE_HPP__
#define __SOC_BASE_HPP__

#include <cstddef>
#include <functional>


namespace SOC {

    /** A class representing either a symbolic or concrete variable */
    struct Base {
      protected:
        /** Constructor */
        Base(const std::size_t h);

      public:
        /** Returns true if this is symbolic */
        virtual bool symbolic() const noexcept = 0;

        /** A hash for this object */
        const std::size_t hash;
    };

} // namespace SOC

// Allow std::hash to work with our object
// Note: This is the recommended way of doing this
namespace std {

    /** Explicit template specialization of std::hash */
    template <> struct hash<SOC::Base> {

        /** Define the hash functor */
        std::size_t operator()(const SOC::Base &b) const noexcept;
    };

} // namespace std

#endif
