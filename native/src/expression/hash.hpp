/**
 * @file
 * @brief This file defines the hash function for Expressions
 */
#ifndef __EXPRESSION_HASH_HPP__
#define __EXPRESSION_HASH_HPP__

#include "constants.hpp"

#include <array>
#include <type_traits>
#include <typeinfo>


namespace Expression {

    // Forward declaration
    class Base;

    /** This function hashes it's arguments */
    template <typename T, typename... Args> Hash hash(Args &&...args) {
        static_assert(std::is_base_of_v<Base, T>, "T must be an Expression");
        secure_hash(

            typeid(T).name(), hash_each(std::forward<Args>(args)...));
    }

    /** A specialization that takes a subclass of Base that has no arguments*/
    template <typename T, std::enable_if_t<std::is_base_of_v<Base, T>, int> = 0> Hash hash() {
        return secure_hash(std::array<Hash, 1> { typeid(T).name() });
    }

} // namespace Expression

#endif
