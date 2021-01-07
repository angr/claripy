/**
 * @file
 * @brief This file defines a templated using which converts an Expression non-raw type to its raw
 * type
 */
#ifndef __EXPRESSION_PRIVATE_RAW_HPP__
#define __EXPRESSION_PRIVATE_RAW_HPP__

#include <memory>


namespace Expression::Private {

    /** This maps an shared_ptr T, to the type it is pointing to */
    template <typename T>
    using Raw = typename std::remove_pointer<decltype(std::declval<T>().get())>::type;

} // namespace Expression::Private

#endif
