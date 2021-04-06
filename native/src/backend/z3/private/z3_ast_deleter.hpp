/**
 * @file
 * @brief This file defines a custom deleter class for a z3 ast object
 */
#ifndef __BACKEND_Z3_PRIVATE_Z3ASTDELETER_HPP__
#define __BACKEND_Z3_PRIVATE_Z3ASTDELETER_HPP__

#include "../tl_context.hpp"


namespace Backend::z3::Private {

    /** A custom deleter for a shared pointer ot a z3 AST
     *  This deleter hooks the z3 reference counting
     */
    struct Z3ASTDeleter final {

        // Default implicits
        SET_IMPLICITS(Z3ASTDeleter, default);

        /** The function which is invoked upon deletion */
        inline void operator()(const z3::Z3_AST del) { z3::z3_dec_ref(del, tl_context); }
    };

} // namespace Backend::z3::Private

#endif
