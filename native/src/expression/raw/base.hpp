/**
 * @file
 * @brief This file defines the base expression
 */
#ifndef __EXPRESSION_RAW_BASE_HPP__
#define __EXPRESSION_RAW_BASE_HPP__

#include "macros.hpp"

#include "../../annotation.hpp"
#include "../hash.hpp"
#include "../private/factory_cache.hpp"

#include <vector>


namespace Expression {

    // Forward declarations
    template <typename T, typename... Args> T factory(Args &&...args);

    namespace Raw {

        /** The base Expression type
         *  All expressions must subclass this
         */
        class Base {
            EXPRESSION_RAW_INIT(Base)
          public:
            /************************************************/
            /*                Pure Virtuals                 */
            /************************************************/

            /** Return true if and only if this expression is symbolic */
            virtual bool symbolic() const = 0;

            /** Get the op of the expression */
            virtual Constants::CCSC op() const = 0;

            /** Get the type of the expression */
            virtual Constants::CCSC type() const = 0;

            /************************************************/
            /*                 Non-Virtuals                 */
            /************************************************/

            std::string full_type_name() const;

            /************************************************/
            /*                Representation                */
            /************************************************/

            /** The hash of the Expression */
            const Hash::Hash id;

            /** A set of annotations applied onto this Expression */
            const std::vector<Annotation::Base> annotations;

          protected:
            /************************************************/
            /*                 Constructors                 */
            /************************************************/

            /** This constructor must exist for compilations reasons
             *  It should never be explicitly called, however, and will throw and error
             *  This exists because the diamond problem mandates non-most-derived nodes within a
             * diamond to be capable of invoking a constructor even though only the diamond bottom
             * class will be able to invoke the diamond top base constructor
             */
            Base();

            /** A protected constructor to disallow public creation */
            explicit Base(const Hash::Hash h, std::vector<Annotation::Base> &&ans = {});
        };

    } // namespace Raw

    // Create a shared pointer alias
    EXPRESSION_RAW_DECLARE_SHARED(Base, Raw)

} // namespace Expression

#endif
