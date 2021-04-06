/**
 * @file
 * @brief This file defines a reference counted backend object
 */
#ifndef __BACKEND_Z3_TORCSHAREDPOINTER_HPP__
#define __BACKEND_Z3_TORCSHAREDPOINTER_HPP__

#include "private/z3_ast_deleter.hpp"

#include "../../utils.hpp"

#include <memory>


namespace Backend::z3 {

    // Static checks
    static_assert(std::is_pointer<z3::Z3_AST>, "ThreadBoundZ3Ref assumes z3::Z3_AST is a pointer");
    static_assert(std::is_const<std::remove_pointer<z3::Z3_AST>>,
                  "ThreadBoundZ3Ref assumes z3::Z3_AST is a pointer to a const object");

    /** A raw z3::Z3_AST pointer that is constant */
    using Z3ASTRawPtr = const z3::Z3_AST;

    /** A shared pointer to a constant Z3 AST with a custom deleter */
    using Z3ASTPtr = std::shared_ptr<Z3ASTRawPtr, Private::Z3ASTDeleter>;

    /** Create a shared pointer to a Z3_AST that hooks with Z3's reference counting system
     *  When this shared pointer is destroyed, the AST's Z3 reference counter will be decremented
     */
    inline Z3ASTPtr to_rc_shared_pointer(const z3::Z3_AST ast) {
        z3::Z3_inc_ref(ast, tl_context);
        return { ast };
    }

} // namespace Backend::z3

#endif
