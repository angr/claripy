/**
 * @file
 * @brief This file defines a type that can be constructed by factory
 */
#ifndef R_SRC_FACTORY_FACTORYMADE_HPP_
#define R_SRC_FACTORY_FACTORYMADE_HPP_

#include "private/has_static_cuid.hpp"

#include "../cuid.hpp"
#include "../hash.hpp"
#include "../util.hpp"

#include <type_traits>


/** Allow factory to construct a class
 *  BASE is the same base class as factory's template Base argument
 *  Factory made subclasses that want to be directly constructed by factory must define this
 *  Leaves class in a private access state
 *  Do *NOT* template BASE. CUID's are generated based on line number thus Base<0>
 *  and Base<4> are defined on the same line and thus would have identical class unique IDs
 */
#define FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(BASE)                                                \
    /* The CUID does not need to be used in non-instantiated classes */                            \
    CUID_DEFINE_MAYBE_UNUSED                                                                       \
  private:                                                                                         \
    /** Allow verification to have friend access */                                                \
    friend struct ::Util::Type::Has::constructor_class;                                            \
    /** Allow cache friend access for factory construction */                                      \
    friend class ::Util::WeakCache<Hash::Hash, const BASE>;


namespace Factory {

    /** A type that can be constructed by the factory
     *  All factory constructable types must subclass this
     *  All subclasses that are or have an instantiable subclass constructed via factory
     *	  1. Must include the FACTORY_ENABLE_CONSTRUCTION_FROM_BASE method. Note that
     *		 this also defines a static_cuid
     *  Warning: No virtual destructor; do *not* delete by base class pointer; avoid slicing!
     */
    struct FactoryMade : public Hash::Hashed, public CUID::HasCUID {
        /** Statically check if Base and T can be factor constructed
         *  Warning: This is not a guarantee that these types can be factory constructed
         *  It just does a few useful static checks to help with the compiler error messages
         */
        template <typename Base, typename T, typename... Args>
        [[gnu::always_inline]] static constexpr void static_type_check() noexcept {
            // Inheritance
            static_assert(Util::Type::Is::ancestor<FactoryMade, Base>,
                          "Base must derive from FactoryMade");
            static_assert(Util::Type::Is::ancestor<Base, T>,
                          "T must derive from Base"); // Allow equality
            // Verify static_cuid
            static_assert(Private::has_static_cuid<T>,
                          "Factory cannot construct anything without a static_cuid");
            static_assert(std::is_same_v<const CUID::CUID, decltype(T::static_cuid)>,
                          "T::static_cuid must be of type const CUID::CUID");
            // Constructor
            // Note: We use has_constructor to pass if the desired constructor is private
            static_assert(Util::Type::Has::constructor<T, const Hash::Hash &, Args &&...>,
                          "T does not have a constructor T{const Hash::Hash &, Args...}");
        }

      protected:
        /** Constructor; allows passing h & c without constructing temporary supers */
        explicit constexpr FactoryMade(const Hash::Hash &h, const CUID::CUID &c) noexcept
            : Hashed { h }, HasCUID { c } {}
        /** Prevent most slicing */
        inline ~FactoryMade() noexcept = default;
        // Rule of 5
        DEFINE_IMPLICITS_CONST_MEMBERS_ALL_NOEXCEPT(FactoryMade);
    };

} // namespace Factory

#endif
