/**
 * @file
 * @brief This file defines the underling hash function for Expressions
 */
#ifndef __EXPRESSION_HASH_UNDERLYING_HPP__
#define __EXPRESSION_HASH_UNDERLYING_HPP__

#include <functional>
#include <string>


namespace Expression::Hash {

    /** Modular hash function or functor
     *  @todo Use a real hash function
     */
    constexpr const auto hasher { std::hash<std::string> {} };

    /** The hash type */
    using Hash = decltype(hasher(0));

} // namespace Expression::Hash

#endif
