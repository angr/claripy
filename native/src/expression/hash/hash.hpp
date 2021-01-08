/**
 * @file
 * @brief This file defines the hash function for Expressions
 */
#ifndef __EXPRESSION_HASH_HASH_HPP__
#define __EXPRESSION_HASH_HASH_HPP__

#include "singular.hpp"
#include "underlying.hpp"

#include <sstream>
#include <type_traits>
#include <typeinfo>


namespace Expression {

    // Forward declaration
    namespace Raw {
        class Base;
    }
    using Base = std::shared_ptr<Raw::Base>;

    namespace Hash {

        /** The hash type */
        using Hash = decltype(std::hash<int> {}(0));

        /** This function hashes it's arguments */
        template <typename T, typename... Args> Hash hash(const Args &...args) {
            static_assert(std::is_base_of_v<Base, T>, "T must be an Expression");
            std::ostringstream input;
            input << typeid(T).name();
            (input << ... << singular(args));
            return hasher(input.str());
        }

        /** A specialization that takes a subclass of Base that has no arguments*/
        template <typename T, std::enable_if_t<std::is_base_of_v<Base, T>, int> = 0> Hash hash() {
            return hasher(typeid(T).name());
        }

    } // namespace Hash

} // namespace Expression

#endif
