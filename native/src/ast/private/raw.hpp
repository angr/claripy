/**
 * @file
 * @brief This file defines a templated using which converts an AST non-raw type to its raw type
 */
#ifndef __AST_PRIVATE_RAW_HPP__
#define __AST_PRIVATE_RAW_HPP__

#include <memory>


/** A namespace used for the ast directory */
namespace AST {

    /** A namespace used to designate certain items in ast as private
     *  These functions should not be called outside of the ast directory
     *  This is useful for helper functions templated functions call
     */
    namespace Private {

        /** This maps an shared_ptr T, to the type it is pointing to */
        template <typename T>
        using Raw = typename std::remove_pointer<decltype(std::declval<T>().get())>::type;

    } // namespace Private

} // namespace AST

#endif
