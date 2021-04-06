/**
 * @file
 * @brief This file defines the z3 backend
 */
#ifndef __BACKEND_Z3_TLCONTEXT_HPP__
#define __BACKEND_Z3_TLCONTEXT_HPP__


namespace Backend::Z3 {

    /** Thread local Z3 context
     *  TODO: figure out if this is a pointer or what
     */
    inline thread_local z3::Context context {}; // TODO: figure out if this is a pointer or what

} // namespace Backend::Z3

#endif
