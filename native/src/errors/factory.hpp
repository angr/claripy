/**
 * @file
 * @brief This file contains the claricpp error factory
 */
#ifndef __ERRORS_FACTORY_HPP__
#define __ERRORS_FACTORY_HPP__

#include "claricpp.hpp"


/** A namespace used for the errors directory */
namespace Errors {

    /** A factory to create a subclass of Claricpp with message msg
     *  There must exist an assignment operator(std::string, const S)
     */
    template <class T, class S> Claricpp factory(const S msg) {
        T ret;
        ret.set(msg);
        return std::move(ret);
    }
} // namespace Errors

#endif
