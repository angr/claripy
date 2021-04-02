/**
 * @file
 * @brief This file defines a reference counted backend object
 */
#ifndef __BACKEND_Z3_ABSTRACT_HPP__
#define __BACKEND_Z3_ABSTRACT_HPP__

#include "../../utils.hpp"


namespace Backend::z3 {

    /** A reference counted Z3_AST which should *never* be shared with any other thread
     *  In debug mode, this will verify that this object is in the correct thread.
     */
    class ThreadBoundZ3Ref final {
      public:
#ifdef DEBUG
    /** A local macro defined a macro to set ctx_ptr to val if DEBUG is defined
     *  Otherwise this macro is a no-op
     */
    #define CTX_PTR(VAL)                                                                          \
        , ctx_ptr { VAL }
#else
    // Definition if debug mode is off
    #define CTX_PTR(_)
#endif

        /** Constructor */
        ThreadBoundZ3Ref(const z3::AST a)
            :
#ifdef DEBUG
              ast {
            a,
                [self = this] {
                    self->verify_thread();
                    z3::z3_dec_ref(ast, tl_context);
                },
                ctx_ptr { &tl_context } {
#else
              ast { a, non_debug_deleter } {
#endif
                z3::Z3_inc_ref(ast, tl_context);
            }

            /** Copy Constructor */
            ThreadBoundZ3Ref(const ThreadBoundZ3Ref &old) : ast { old } CTX_PTR(old.ctx_ptr) {
                verify_thread();
            }

            /** Move Constructor */
            ThreadBoundZ3Ref(const ThreadBoundZ3Ref &old) NOEXCEPT_UNLESS_DEBUG :
                ast { old } CTX_PTR(std::move(old.ctx_ptr)) {
                verify_thread();
            }

            /** Destructor */
            ~ThreadBoundZ3Ref() { verify_thread(); }

          private:
            /** Delete default constructor */
            ThreadBoundZ3Ref() = delete;

            // Delete assignment operators
            SET_IMPLICT_OPERATORS(ThreadBoundZ3Ref, delete);

#ifndef DEBUG
            /** Shared pointer deleter helper function for non-debug mode
             *  @todo: Is this noexcept?
             */
            static non_debug_deleter(const z3::AST del) { z3::z3_dec_ref(del, tl_context); }
#endif

            /** Throw a WrongThread exception if the thread local context addresses differ
             *  When not in debug mode, this function is a no-op and should be optimized away
             */
            inline void verify_thread() NOEXCEPT_UNLESS_DEBUG const {
#ifdef DEBUG
                using Err = Utils::Error::Unexpected::WrongThread;
                Utils::affirm<Err>(
                    ctx_ptr == &tl_context,
                    "ThreadBoundRef found in a different thread than it was constructed in");
#endif
            }

            // Internal Types

            // Static checks
            static_assert(std::is_pointer<z3::Z3_AST>,
                          "ThreadBoundZ3Ref assumes z3::Z3_AST is a pointer");

            /** The type z3::Z3_AST points to */
            using RawZ3AST = std::remove_pointer_t<z3::Z3_AST>;

            // Representation

            /** A shared pointer to a *z3_AST */
            const std::shared_ptr<const RawZ3AST> ast;
#ifdef DEBUG
            /** The address of the thread_local context in which this object was constructed */
            Constants::CTSC<z3::context> ctx_ptr;
#endif

// Cleanup
#undef CTX_PTR
        };


    } // namespace Backend::z3

#endif
