/**
 * @file
 * @brief This file defines the underling hash function for Expressions
 */
#ifndef __EXPRESSION_HASH_SINGULAR_HPP__
#define __EXPRESSION_HASH_SINGULAR_HPP__

#include "../../constants.hpp"

#include <memory>
#include <string>
#include <vector>


// Forward declarations
namespace Annotation {
    struct Base;
}

namespace Expression::Hash {

    /** A struct used to allow different return types of singular depending on T
     *  The general case is undefined, specializations must be defined
     */
    template <typename> struct SingularRetMap;

    /** Determines how hash handles the type passed
     *  This hash does not need to be a real hash, it just has to represent T as an SRet<T>
     *  which will be appened to a stringstream that will be properly hashed
     *  The general case is undefined, specializations must be defined
     */
    template <typename T> typename SingularRetMap<T>::RetType singular(const T &);

    /** A specialization for T = Constants::Int */
    template <> struct SingularRetMap<Constants::Int> { using RetType = Constants::Int; };

    /** A specialization for T = char * */
    template <> struct SingularRetMap<char *> { using RetType = Constants::CCS; };

    /** A specialization for T = std::vector<std::shared_ptr<Annotation>> */
    template <> struct SingularRetMap<std::vector<std::shared_ptr<Annotation::Base>>> {
        using RetType = std::string;
    };

} // namespace Expression::Hash

#endif
