/**
 * @file
 * @brief This file defines the Expression::Raw::Type::Base class
 */
#ifndef __EXPRESSION_RAW_TYPE_BASE_HPP__
#define __EXPRESSION_RAW_TYPE_BASE_HPP__

#include "macros.hpp"

#include "../../../macros.hpp"
#include "../../constants.hpp"
#include "../../simplified_level.hpp"
#include "../base.hpp"

#include <list>
#include <map>
#include <memory>
#include <string>
#include <vector>


namespace Expression {

    // Forward declarations
    class CacheKey;
    template <typename T, typename... Args>
    T factory(std::set<BackendID> &&eager_backends, Args &&...args);
    namespace Private {
        template <typename A, typename B> class Cache;
    }

    // These types should be wrapped by a shared pointer when used
    // A factory is used to construct them and handle hash caching
    namespace Raw::Type {

        /** This is the base class of all typed Expressions.
         *  An Expression tracks a tree of operations on arguments.
         *  This class should not be instanciated directly - instead, use one of the
         *  constructor functions (BVS, BVV, FPS, FPV...) to construct a leaf node and then
         *  build more complicated expressions using operations. Expression objects have *hash
         *  identity*. This means that an Expression that has the same hash as another Expression
         *  will be the *same* object. This is critical for efficient memory usage. As an example,
         *  the following is true:: a, b = two different Expressions c = b + a d = b + a assert c
         *  is d
         */
        class Base : public ::Expression::Raw::Base {
            EXPRESSION_RAW_TYPE_INIT_EXPRESSION_BASE_SUBCLASS(Base)
          public:
            /** Returns a string representation of this */
            virtual std::string repr(const bool inner = false, const Constants::Int max_depth = -1,
                                     const bool explicit_length = false) const;

            /************************************************/
            /*                Representation                */
            /************************************************/

            /** The hash of the Expression
             *  This variable is intentionally declared first as we want it to be the first
             * argument passed to the Base() constructor; since it was declared first most
             * compilers will issue a warning if it is not set before all other member variables */
            const Hash id;

#if 0
            /** A measure of how simplified this Expression is */
            const SimplifiedLevel simplified;

            /** A set of backents that are known to be unable to handle this Expression */
            const std::set<BackendID> errored_backends;
#endif

          protected:
            /************************************************/
            /*                 Constructors                 */
            /************************************************/

            /** A protected constructor to disallow public creation
             *  This must have take in the same arguments types as the hash function, minus the
             * hash These arguments may be taken in via copy, reference or move; ownership is given
             */
            Base(const Hash h);

          private:
            /************************************************/
            /*                   Statics                    */
            /************************************************/

            /** The hash function of this Expression
             *  This must have take in the same arguments as the constructor, minus the hash
             *  These arguments args must be const values or references; this function must be pure
             */
            static Hash hash();

            /** Declare CacheKey a friend */
            friend class ::Expression::CacheKey;
        };

    } // namespace Raw::Type

} // namespace Expression

#endif
