/**
 * @file
 * @brief This file defines a type that can be constructed by factory
 */
#ifndef __FACTORY_FACTORYMADE_HPP__
#define __FACTORY_FACTORYMADE_HPP__

#include "private/has_static_cuid.hpp"

#include "../cuid.hpp"
#include "../hash.hpp"
#include "../utils.hpp"

#include <type_traits>


/** Allow factory to construct a class
 *  BASE is the same base class as factory's template Base argument
 *  Factory made subclasses that want to be directly constructed by factory must define this
 *  Leaves class in a private access state
 */
#define FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(BASE)                                               \
    /* The CUID does not need to be used in non-instantiated classes */                           \
    DEFINE_MAYBE_UNUSED_STATIC_CUID                                                               \
  private:                                                                                        \
    /** Allow verification to have friend access */                                               \
    template <typename, typename...> friend struct ::Utils::HasConstructor;                       \
    template <typename, typename...> friend struct ::std::is_constructible;                       \
    /** Allow cache friend access for factory construction */                                     \
    friend class ::Utils::Cache<Hash::Hash, const BASE>;


namespace Factory {

    /** A type that can be constructed by the factory
     *  All factory constructable types must subclass this
     *  All subclasses that are or have an instantiable subclass constructed via factory
     *	  1. Must include the FACTORY_ENABLE_CONSTRUCTION_FROM_BASE method. Note that
     *		 this also defines a static_cuid
     */
    struct FactoryMade : public Hash::Hashed, public CUID {

        /** Constructor */
        explicit inline FactoryMade(const Hash::Hash &h, const Constants::UInt &c) noexcept
            : Hashed { h }, CUID { c } {}

        /** Statically check if Base and T can be factor constructed
         *  Warning: This is not a gaurntee that these types can be factory constructed
         *  It just does a few useful static checks to help with the compiler error messages
         */
        template <typename Base, typename T, typename... Args>
        [[gnu::always_inline]] static constexpr void static_type_check() noexcept {
            // Inheretence
            static_assert(Utils::is_ancestor<FactoryMade, Base>,
                          "Base must derive from FactoryMade");
            static_assert(Utils::is_ancestor<Base, T>,
                          "T must derive from Base"); // Allow equality
            // Verify static_cuid
            static_assert(Private::has_static_cuid<T>,
                          "Factory cannot construct anything without a static_cuid");
            static_assert(Utils::is_exactly_same<const Constants::UInt, decltype(T::static_cuid)>,
                          "T::static_cuid must be of type Constants::UInt");
            // Constructor
            // Note: We use has_constructor to pass if the desired constructor is private
            static_assert(Utils::has_constructor<T, const Hash::Hash &, Args &&...>,
                          "T does not have a constructor T(const Hash::Hash &, Args...");
        }

      protected:
        /** Pure virtual destructor */
        inline ~FactoryMade() noexcept override = 0;

        // Rule of 5
        SET_IMPLICITS_CONST_MEMBERS(FactoryMade, default, noexcept)
    };

    /** Default virtual destructor */
    FactoryMade::~FactoryMade() noexcept = default;

} // namespace Factory

#endif
