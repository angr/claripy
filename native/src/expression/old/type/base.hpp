/**
 * @file
 * @brief This file defines the Expression::Raw::Type::Base class
 */
#ifndef __EXPRESSION_RAW_TYPE_BASE_HPP__
#define __EXPRESSION_RAW_TYPE_BASE_HPP__

#include "../../../macros.hpp"
#include "../base.hpp"


namespace Expression {

    // Forward declarations
    class CacheKey;

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
        class Base : virtual public ::Expression::Raw::Base {
            EXPRESSION_RAW_ABSTRACT_INIT_IMPLICIT_CTOR(Base)
            /** Declare CacheKey a friend */
            friend class ::Expression::CacheKey;
        };

    } // namespace Raw::Type

} // namespace Expression

#endif
